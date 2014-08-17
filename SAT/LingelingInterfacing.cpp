/**
* @file LingelingInterfacing.cpp
* Implements class LingelingInterfacing
* @author Ioan Dragan
*/

#include "Debug/Assertion.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/System.hpp"

#include "SATInference.hpp"
#include "SATClause.hpp"
#include "SATLiteral.hpp"

#include "LingelingInterfacing.hpp"

#include "Shell/Options.hpp"

#include "LingelingInterfacing.hpp"
#include "TWLSolver.hpp"
#include "MinimizingSolver.hpp"

#include <csignal>

extern "C" {
	#include "lglib.h"
	#include <unistd.h>
#include <signal.h>
}

/**
 * Just as a general hint: assuming one wants to trace all the API calls to Lingeling
 * can be done by enabling the LGLAPITRACE=filename from command line. Doing so
 * Lingeling will produce a trace file (filename) with all the calls to its API.
 *
 * e.g: LGLAPITRACE=trace ./vampire options to Vampire
 */
namespace SAT
{
using namespace std;
using namespace Lib;
//signal handlers taken from lglmain.c
static LGL * lgl4sigh;

/*
 * Constructor for that creates an object containing the Lingeling solver based on the options
 * @opt provided as parameter
 *
 * Note that through out the entire Lingeling integration we shift the SAT variables by one. This means that as
 * soon as we get a new variable that has to be added to Lingeling we add 1 to it. We do this in order
 * to avoid the situation where we would have a variable 0 that has to be added to Lingeling. Adding 0
 * to Lingeling has the DIMACS meaning of terminating a clause.
 * TODO: investigate if the shifting by one can be removed.
 */
LingelingInterfacing::LingelingInterfacing(const Options& opt,
		bool generateProofs) :
		_generateProofs(generateProofs), _hasAssumptions(false)
{
	CALL("LingelingInterfacing::LingelingInterfacing");
	//here we should take care of all the options passed from the caller
	//TimeCounter ntc(TC_LINGELING);
	Options _opts(opt);

	lgl4sigh = _solver = lglinit();
	//setsighandlers ();
	Lib::System::setSignalHandlers();
	//for debugging
	lglsetopt(_solver, "verbose", -1);
	lglsetopt(_solver, "log", -1);
	lglsetopt(_solver, "drup", -1);
	lglsetopt(_solver, "plain", 0);
	//lglsetopt(_solver, "dlim",0);
	size_t remMem =env.options->memoryLimit() - (Allocator::getUsedMemory()/1048576);
	lglsetopt(_solver, "memlim", remMem);
	
	//set signal handler for ABORTIF
	//sig_abort_handler = signal(LING_SIG, alert_abort);
	//set the conflict limit -1 => unlimited
	//this could also be controlled by the opt
	lglsetopt(_solver, "clim", -1);

	//set the decision limit default -1 => unlimited
	lglsetopt(_solver, "dlim", -1);

	//set the propagation limit default value -1 => thousands
	lglsetopt(_solver, "plim", -1);

	//the flipping option allows us to get similar models if they exist, minimal change
	if (env.options->satLingelingSimilarModels())
	{
		lglsetopt(_solver, "flipping", 0);
	}
	_status = SATSolver::UNKNOWN;
	//TODO maybe better way to do this!
	_refutation = 0;
	_clauseList = 0;
	_assumptions = 0;
	_satVariables = 0;
}

LingelingInterfacing::~LingelingInterfacing()
{
	CALL("LingelingInterfacing::~LingelingInterfacing");
	//release the memory used by lingeling
	lglrelease(_solver);
}

void LingelingInterfacing::addClauses(SATClauseIterator clauseIterator,
		bool onlyPropagate)
{
	CALL("LingelingInterfacing::addClause(SatClauseIte, bool onlyPropagate)");
	//TAKE CARE HOW ONE ADDS CLAUSES. a call to lgladd(_solver, 0) terminates the cluase
	TimeCounter tc(TC_LINGELING);
	//iterate over all the clauses from the problem
	//if the solver is in UNSATISFIABLE state, adding a new clause keeps it unsatisfiable so simply return
	if (_status == SATSolver::UNSATISFIABLE){
		return;
	}

	try{
		// Limit memory to what the Allocator has not used up
		size_t remMem =env.options->memoryLimit() - (Allocator::getUsedMemory()/1048576);
		if(onlyPropagate){
			lglsetopt(_solver,"clim",1);
		} else {
			lglsetopt(_solver,"clim",-1);
		}
		lglsetopt(_solver,"memlim",remMem);

		addClausesToLingeling(clauseIterator);
		//add statistics about usage of Lingeling
		//total time spent by  Lingeling in solving
	}
	catch (const UnsatException& e){
		_status = SATSolver::UNSATISFIABLE;
		_refutation = e.refutation;
	}
	catch (TimeLimitExceededException&){
		env.statistics->terminationReason = Statistics::TIME_LIMIT;
		env.timeLimitReached();
		env.checkTimeSometime<64>();
		throw TimeLimitExceededException();
	}
	env.checkTimeSometime<64>();
}

void LingelingInterfacing::setSolverStatus(unsigned int status)
{
	CALL("LingelingInterfacing::setSolverStatus(uint status)");
	switch (status)
	{
	case LGL_UNKNOWN:
		_status = SATSolver::UNKNOWN;
		break;
	case LGL_SATISFIABLE:
		_status = SATSolver::SATISFIABLE;
		break;
	case LGL_UNSATISFIABLE:
		_status = SATSolver::UNSATISFIABLE;
		break;
	default:
		ASSERTION_VIOLATION;
		break;
	}
}

void LingelingInterfacing::addClausesToLingeling(SATClauseIterator iterator) {
	CALL("LingelingInterfacing::addClausesToLingeling");
	SATLiteralStack literalStack;
	literalStack.reset();

	//check how much time we spent already and set the maximum allowed for sat
	int remaining = env.remainingTime();

	env.statistics->phase = Statistics::SAT_SOLVING;
	//TimeCounter ntc(TC_OTHER);

	//convert the remaining time from miliseconds to seconds
	//in general Vampire uses miliseconds. But lingeling uses seconds.
	//this means, if we have less than a second left for SAT solving, allow
	//one second run time.
	//set the alarm handlers for sat solver
	if (remaining < 1) {
		//update statistics
		Timer::syncClock();
		remaining = 1;
	}

	alarm(double(remaining / 1000));
	DHMap<SATLiteral, List<int>*> mapLitToClause;
	mapLitToClause.reset();

	//SATClauseList *clauseList=0;
	unsigned int result;
	int clauseIdx = 0;
	//in order to properly accommodate SSplitingBranchSelector::flush() one has to
	//check whether the iterator is empty. And if so call for satisfiability check
	//if this check is not done, SIGABT due to lglderef() => not SATISFIED | EXTENDED
	if (!iterator.hasNext()) {
		env.statistics->satLingelingSATCalls++;
		result = lglsat(_solver);
		setSolverStatus(result);
		return;
	}

	while (iterator.hasNext()) {
		SATClause* currentClause = iterator.next();

		//add the statistics for Lingeling total number of clauses
		env.statistics->satLingelingClauses++;

		SATClauseList::push(currentClause, _clauseList);

		//treat each of the clauses individually.
		ASS_GE(currentClause->length(), 1);

		SATClause::Iterator ccite(*currentClause);
		while (ccite.hasNext()) {
			SATLiteral sLit = ccite.next();
			//currVar refers to the current variable
			unsigned currVar = sLit.var() + 1;

			if (_litToClause.find(currVar) != true) {
				SATClauseList *clauseList = 0;
				clauseList = clauseList->cons(currentClause);
				_litToClause.insert(currVar, clauseList);
				_satVariables = _satVariables->cons(currVar);
				//increase the counter of variables added to Lingeling
				env.statistics->satLingelingVariables++;
				//_satVariables.addLast(currVar);
			} else {
				SATClauseList *scl = _litToClause.get(currVar);
				scl = scl->cons(currentClause);
				_litToClause.set(currVar, scl);
			}

			ASS(lglusable(_solver, currVar));
			int8_t polarity = (sLit.isNegative() ? -1 : 1 );
			lgladd(_solver, polarity * currVar);
			lglfreeze(_solver, currVar);
		}

		//add the marker for clause termination
		lgladd(_solver, 0);

		clauseIdx++;
		if (env.options->satLingelingIncremental() == true) {
			env.statistics->phase = Statistics::SAT_SOLVING;
			//increment the number of calls to satisfiability check
			env.statistics->satLingelingSATCalls++;
			//call lingeling satisfiability check
			result = lglsat(_solver);
			env.checkTimeSometime<64>();
			setSolverStatus(result);
			Timer::syncClock();

			switch(result){
			case LGL_UNSATISFIABLE:
				setRefutation();
				throw UnsatException(_refutation);
				break;
			case LGL_SATISFIABLE:
				_status = SATSolver::SATISFIABLE;
				break;
			case LGL_UNKNOWN:
				_status = SATSolver::UNKNOWN;
				break;
			default:
				ASSERTION_VIOLATION;
			}
		}
	}

	if (env.options->satLingelingIncremental() == false) {
		env.statistics->phase = Statistics::SAT_SOLVING;
		//increment lingeling call for satisfiability check statistics
		env.statistics->satLingelingSATCalls++;
		//call for satisfiability check
		result = lglsat(_solver);
		env.checkTimeSometime<64>();
		setSolverStatus(result);
		Timer::syncClock();
		if (result == LGL_UNSATISFIABLE) {
			setRefutation();
			throw UnsatException(_refutation);
		}

		if (result != LGL_SATISFIABLE) {
			setSolverStatus(result);
		}
	}


}

/**
 * The reasoning behind this implementation is as follows:
 * If the SAT solver manages to prove the problem unsatisfiable, it means that it managed
 * to find a conflict (contradiction) at decision level 0. Hence, using just the clauses
 * that have variables assigned at decision level 0 makes sense. In our case that can be
 * tested by lglfixed call. And by doing so, the set of clauses that are sent back to the
 * first-order reasoning part (as refutation) could be smaller than the actual problem.
 * This is not guaranteed though.
 */
void LingelingInterfacing::setRefutation(){
	CALL("LingelingInterfacing::setRefuation");

	SATLiteralStack resList;
	resList.reset();

	SATClauseList* premises = 0 ;
	SATClause *res = SATClause::fromStack(resList);

	//one could also minimize this set
	//premises = _clauseList;

	List<unsigned>::Iterator varit(_satVariables);
	while(varit.hasNext()){
		unsigned var = varit.next();
		if(lglfixed(_solver, var)){
			SATClauseList *scl = _litToClause.get(var);
			SATClauseList::Iterator ite(scl);
			while(ite.hasNext()){
				SATClause* clause = ite.next();
				if(!premises->member(clause)){
					premises = premises->cons(ite.next());
				}
			}
		}
	}
	//in case we also have assumptions we have to add them all to the premises.
	if(hasAssumptions()){
		//in case we have assumptions we have to add them to the refutation as well
		SATLiteralStack sls;
		List<SATLiteral*>::Iterator slite(_assumptions);
		while(slite.hasNext()){
			SATLiteral* sl = slite.next();
			sls.push(*sl);
		}
		SATClause* assumptionClause = SATClause::fromStack(sls);
		premises = premises->cons(assumptionClause);
	}

	ASS(premises);
	SATInference* inf = new PropInference(premises);
	res->setInference(inf);
	_refutation = res;
	_status = SATSolver::UNSATISFIABLE;
}

void LingelingInterfacing::printAssignment()
{
	CALL("LingelingInterfacing::printAssignment");

	ASS(_status == SATSolver::SATISFIABLE);
	DArray<AsgnVal> _assignm;
	int maxVar = lglmaxvar(_solver);
	_assignm.expand(maxVar, AS_UNDEFINED);

	for (int var = 0; var < maxVar; var++)
	{
		switch (lglderef(_solver, var+1))
		{
		case -1:
			_assignm[var] = AS_FALSE;
			break;
			// _res=_res->addLast(AS_FALSE); break;
		case 1:
			_assignm[var] = AS_TRUE;
			break;
			//_res=_res->addLast(AS_TRUE);break;
		case 0:
			_assignm[var] = AS_UNDEFINED;
			break;
			//_res=_res->addLast(AS_UNDEFINED);break;
		default:
			ASSERTION_VIOLATION;
		}
	}
}

//as this function is used, we only assume single units
//lingeling allows us to also assume more than units, clauses
void LingelingInterfacing::addAssumption(SATLiteral literal,
		unsigned conflictCountLimit) {
	CALL("LingelingInterfacing::addAssumption(SATLiteral, unsigned condlictCountLimit)");
	TimeCounter tc(TC_LINGELING);
	env.statistics->satLingelingAssumptions++;
	//in case the solver is in UNSATISFIABLE state don't assume the literal
	if (_status == SATSolver::UNSATISFIABLE) {
		return;
	}

	if (_hasAssumptions) {
		List<SATLiteral*>::Iterator lite(_assumptions);
		while (lite.hasNext()) {
			SATLiteral *slite = lite.next();
			if ((slite->var() + 1) == 0) {
				ASSERTION_VIOLATION;
			}
			int8_t polarity = slite->isNegative() ? -1 : 1 ;
			lglassume(_solver, polarity * (slite->var()+1));
		}
	}
	//if the literal has negative polarity then multiply the flag by -1
	int8_t polarity = (literal.isNegative()? -1 : 1);
	//assume the literal
	if ((polarity * (literal.var() + 1)) == 0){
		ASSERTION_VIOLATION;
	}

	double remaining = env.remainingTime();
	if (remaining < 1) {
		//throw TimeLimitExceededException();
		remaining = 1;
		Timer::syncClock();
	}
	//set an alarm with the remaining time
	alarm((remaining / 1000));

	lglassume(_solver, (polarity * (literal.var() + 1)));
	env.statistics->satLingelingSATCalls++;
	unsigned int result = lglsat(_solver);
	env.checkTimeSometime<64>();
	setSolverStatus(result);
	Timer::syncClock();
	if (result == LGL_UNSATISFIABLE) {
		setRefutation();
		_status = SATSolver::UNSATISFIABLE;
		throw UnsatException(_refutation);
	}

	if (result == LGL_SATISFIABLE) {
		_status = SATSolver::SATISFIABLE;

	} else {
		_status = SATSolver::UNKNOWN;
	}

	_assumptions = _assumptions->cons(&literal);
	_hasAssumptions = true;
}

//since lingeling allows assumption of clauses, let's have a function which does that
void LingelingInterfacing::addCAssumption(SATClause* clause,
		unsigned conflictCountLimit)
{
	CALL("LingelingInterfacing::addaCAssumption");
	if (_status == SATSolver::UNSATISFIABLE)
	{
		return;
	}
	unsigned clauseLength = clause->length();

	for (unsigned idx = 0; idx < clauseLength; idx++)
	{
		SATLiteral sLit = (*clause)[idx];
		unsigned currVar = sLit.var()+1;
		//take care of the polarity of each of the literals
		int8_t polarity = (sLit.isNegative() ? -1 : 1);
		//assume each of them with the right polarity
		lglcassume(_solver, polarity * currVar);
		//add the end of lglcassume
		lglcassume(_solver, 0);
	}
	//something we could do is book-keeping of what we add and which fails!
}
/**
 * get the assigment for @param var
 */
SATSolver::VarAssignment LingelingInterfacing::getAssignment(unsigned var)
{
	CALL("LingelingInterfacing::getAssignment(var)");
	ASS(_status == SATISFIABLE);
	int val;

	val = lglderef(_solver, var+1);
	switch (val)
	{
	case -1:
		return SATSolver::FALSE;
	case 1:
		return SATSolver::TRUE;
	case 0:
		return SATSolver::DONT_CARE;
	default:
		ASSERTION_VIOLATION;
	}
	//Added just in order to get rid of compiler warning!
	return SATSolver::DONT_CARE;
}

void LingelingInterfacing::retractAllAssumptions()
{
  CALL("LingelingInterfacing::retractAllAssumptions()");
  //in the case of Lingeling all the assumptions are valid only until the next lslsat/lglsimp
  //so we do not have to worry about retracting assumptions.
  //but we still have to mark that at this point there are no more assumptions
  _hasAssumptions = false;
  if (_assumptions->isEmpty())
	  return;
  //remove all the assumptions from the 
  while(_assumptions->isNonEmpty()){
    List<SATLiteral*>::pop(_assumptions);
  }
}

bool LingelingInterfacing::hasAssumptions() const
{
  CALL("LingelingInterfacing::hasAssumptions()");
  return _hasAssumptions;
}

SATClause* LingelingInterfacing::getRefutation()
{
	CALL("LingelingInterfacing::getRefutation");
	ASS(_status == SATSolver::UNSATISFIABLE);
	return _refutation;

}

/**
 * Works by creating a copy of the SAT solver and getting it to solve the problem
 * in a different way
 *
 * Not currently in use - review before using
 */
void LingelingInterfacing::randomizeAssignment()
{
	CALL("LingelingInterfacing::randomizeAssignment()");
	//here we should find a way to randomize the assignment
	//lglsetopt(_solver, "flipping",1);
	TimeCounter tc(TC_LINGELING);
	LGL* clone;
	clone = lglclone(_solver);
	if (hasAssumptions()){
		List<SATLiteral*>::Iterator lite(_assumptions);
		while(lite.hasNext()){
			SATLiteral* lit = lite.next();
			int8_t polarity = (lit->isNegative() ? -1 : 1);
			lglassume(clone, polarity * lit->var());
		}
		unsigned int result = lglsat(clone);
		setSolverStatus(result);
		env.statistics->satLingelingSATCalls++;
		if (lglchanged(clone)){
			_solver = clone;
			lglrelease(clone);
		}
	}
}

void LingelingInterfacing::printLingelingStatistics()
{
	CALL("LingelingInterfacing::printLingelingStatistics");
	lglstats(_solver);
	cout << "conflicts :" << lglgetconfs(_solver) << endl;
	cout << "memory MB: " << lglmb(_solver) << endl;
	cout << "memory Bytes: " << lglbytes(_solver) << endl;
	cout << "seconds : " << lglsec(_solver) << endl;
	cout << "processtime: " << lglprocesstime() << endl;
}
};

//end of the SAT namespace
