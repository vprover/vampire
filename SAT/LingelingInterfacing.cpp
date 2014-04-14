/**
* @file LingelingInterfacing.cpp
* Implements class LingelingInterfacing
*/

#include "Debug/Assertion.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Lib/TimeCounter.hpp"

#include "SATInference.hpp"
#include "SATClause.hpp"
#include "SATLiteral.hpp"

#include "LingelingInterfacing.hpp"

#include <csignal>

extern "C" {
	#include "lglib.h"
	#include <unistd.h>
}


namespace SAT
{
using namespace std;
using namespace Lib;

//signal handling for lingeling
static void (*sig_alrm_handler)(int);
static int caughtalarm = 0;

static void catchlrm(int sig) {
	if (!caughtalarm) {
		caughtalarm = 1;
		throw TimeLimitExceededException();
		}
} 

static int checkalarm(void * ptr){
	ASS(ptr == (void*) &caughtalarm);
	return caughtalarm;
}	//do the set-up of sat solver according to environment options
	LingelingInterfacing::LingelingInterfacing(const Options& opt, bool generateProofs) : 
		_generateProofs(generateProofs), _hasAssumptions(false){
			CALL("LingelingInterfacing::LingelingInterfacing");
			//here we should take care of all the options passed from the caller 
			TimeCounter ntc(TC_SAT_SOLVER);
			Options _opts(opt);
			_solver = lglinit();

			//for debugging 
			lglsetopt(_solver, "verbose",-1);
			lglsetopt(_solver, "plain",1);
			//lglsetopt(_solver, "");
			//lglsetopt(_solver, "dlim",0);
			lglsetopt(_solver, "memlim", env.options->memoryLimit());

			//set the alarm handlers for sat solver
			lglseterm(_solver, checkalarm, &caughtalarm);
			sig_alrm_handler = signal (SIGALRM, catchlrm);

			//check how much time we spent already and set the maximum allowed for sat
			int remaining = env.remainingTime();
			//in general Vampire uses miliseconds. But lingeling uses seconds. 
			//this means, if we have less than a second left for SAT solving, allow 
			//one second run time.
			if (remaining < 1000)
				remaining = 1000;
			//convert the remaining time from miliseconds to seconds
			alarm((remaining/1000));

			//set the conflict limit -1 => unlimited
			lglsetopt(_solver, "clim", -1 );
			//set the decision limit default -1 => unlimited 
			lglsetopt(_solver, "dlim", -1 );
			//set the propagation limit default value -1 => thousands 
			lglsetopt(_solver, "plim", -1);

			//here we should use more than this
			//see picosat.h lines 85-..
	}

	LingelingInterfacing::~LingelingInterfacing(){
		CALL("LingelingInterfacing::~LingelingInterfacing");
		//release the memory used by lingeling
		lglrelease(_solver);
	} 

	void LingelingInterfacing::addClauses(SATClauseIterator clauseIterator, bool onlyPropagate){
		CALL("LingelingInterfacing::addClause(SatClauseIte, bool onlyPropagate)");
		//TAKE CARE HOW ONE ADDS CLAUSES. a call to lgladd(_solver, 0) terminates the cluase
		TimeCounter tc(TC_SAT_SOLVER);
		//iterate over all the clauses from the problem
		//if the solver is in UNSATISFIABLE state, adding a new clause keeps it unsat
		if(_status == SATSolver::UNSATISFIABLE){
			return;
		}
		try{
			//Can we reuse an iterator? I think we need to store it in a Stack	
			static SATClauseStack newClauses;
			newClauses.reset();
			newClauses.loadFromIterator(clauseIterator);

			//store clauses in addedClauses
			_addedClauses.loadFromIterator(SATClauseStack::Iterator(newClauses));

			addClausesToLingeling(pvi(SATClauseStack::Iterator(newClauses)));

		}catch(const UnsatException& e){
			_status = SATSolver::UNSATISFIABLE;
			_refutation = e.refutation;
		}

	}

	void LingelingInterfacing::setSolverStatus(unsigned int status){
		CALL("LingelingInterfacing::setSolverStatus(uint status)");

		switch(status){
		case LGL_UNKNOWN : _status = SATSolver::UNKNOWN; break;
		case LGL_SATISFIABLE : _status = SATSolver::SATISFIABLE; break;
		case LGL_UNSATISFIABLE : _status = SATSolver::UNSATISFIABLE; break;
		default:
			ASSERTION_VIOLATION; break;
		}
	}

	void LingelingInterfacing::addClausesToLingeling(SATClauseIterator iterator){
		CALL("LingelingInterfacing::addClauses(SATClauseIterator iterator)");
		List<unsigned>* varList = 0; 

		while(iterator.hasNext()){
			SATClause * currentClause = iterator.next();
			//treat each of the clauses individually. 
			unsigned clauseLength = currentClause->length();
			ASS_GE(clauseLength, 1);
			for (unsigned idx = 0; idx < clauseLength ; idx++){
			//treat each of the literals individually 
				SATLiteral sLit = (*currentClause)[idx];
				unsigned currVar = sLit.var();
				if(!varList->member(currVar))
					varList = varList->cons(sLit.var());
				//in case our literal is with positive polarity
				lgladd(_solver, (sLit.polarity() ==1 ? currVar : -currVar));
				//TODO freezing of all the literals might not be a good idea!
				//why not reuse here instead of freezing the literals?
				lglfreeze(_solver, currVar);
			}
			//add the marker for clause termination 
			lgladd(_solver, 0);
		}
		unsigned int result = lglsat(_solver);
		setSolverStatus(result);
		//#if VDEBUG
		//if(result == LGL_SATISFIABLE){
		//	printAssignment();
		//}
		//#endif
			
		if(result == LGL_UNSATISFIABLE){
			throw UnsatException();
			}
			
	
	}

	void LingelingInterfacing::printAssignment(){
		CALL("LingelingInterfacing::printAssignment");
		ASS(_status == SATSolver::SATISFIABLE);
		DArray<AsgnVal>_assignm;
		int maxVar = lglmaxvar(_solver);
		_assignm.expand(maxVar, AS_UNDEFINED);
		for (int idx = 1 ; idx <= maxVar; idx++){
			int val;
			val = lglderef(_solver, idx);
			//val = lglfixed(_solver, idx);
			//val = lglfailed(_solver, idx);
			switch (val){
				case -1 : _assignm[idx-1] = AS_FALSE; break;
					// _res=_res->addLast(AS_FALSE); break;
				case 1 : _assignm[idx-1] = AS_TRUE; break;
					//_res=_res->addLast(AS_TRUE);break;
				case 0 : _assignm[idx-1] = AS_UNDEFINED; break;
					//_res=_res->addLast(AS_UNDEFINED);break;
				default : ASSERTION_VIOLATION;
				}
			}
		#if VDEBUG 
		for (int idx = 0; idx < maxVar ; idx++){
			AsgnVal val = _assignm[idx];
			switch(val){
				case AS_FALSE : cout<<idx+1<<" false\n"; break;
				case AS_TRUE : cout<<idx+1<<" true\n"; break;
				case AS_UNDEFINED: cout<<idx+1 << " any value \n"; break;
				default: ASSERTION_VIOLATION;
				}
			}
		#endif
		/*
		List<AsgnVal>::Iterator ite(_res);
		int idx = 0;
		while(ite.hasNext()){
			AsgnVal v = ite.next();
			switch(v){
				case AS_FALSE : cout<<idx+1<<" false\n"; break;
				case AS_TRUE : cout<<idx+1<<" true\n"; break;
				case AS_UNDEFINED: cout<<idx+1 << " any value \n"; break;
				default: 
					ASSERTION_VIOLATION;
				}
				idx++;
			}
			*/
	}

	//as this function is used, we only assume single units
	//lingeling allows us to also assum more than units, clauses
	void LingelingInterfacing::addAssumption(SATLiteral literal, unsigned conflictCountLimit){
		CALL("LingelingInterfacing::addAssumption(SATLiteral, unsigned condlictCountLimit)");
		//in case the solver is in UNSATISFIABLE state don't assume the literal
		if (_status == SATSolver::UNSATISFIABLE) {
			 LOG("sat_asmp","assumption ignored due to unsat state");
			return;
		}
		//if the literal has negative polarity then multiply the flag by -1
		int flag = 1;
		flag = flag * (literal.polarity() == 1 ? 1:-1);
		//assume the literal
		lglassume(_solver, (flag*literal.var()));
		_assumptions = _assumptions->cons(literal);
		_hasAssumptions = true;
	}

	//since lingeling allows assumption of clauses, let's have a function which does that
	void LingelingInterfacing::addCAssumption(SATClause* clause, unsigned conflictCountLimit){
		CALL("LingelingInterfacing::addaCAssumption");
		if(_status == SATSolver::UNSATISFIABLE){
			LOG("sat_asmp", "assumption ignored due to unsat state in CAssumption");
			return;
		}
		unsigned clauseLength = clause->length();

		for(unsigned idx = 0; idx < clauseLength ; idx++){
			SATLiteral sLit = (*clause)[idx];
			unsigned currVar = sLit.var();
			//take care of the polarity of each of the literals
			int polarity = (sLit.polarity() == 1 ? 1 : -1);
			//assume each of them with the right polarity 
			lglcassume(_solver, polarity*currVar);
			//add the end of lglcassume 
			lglcassume(_solver, 0);
		}
		//something we could do is book-keeping of what we add and which fails!
	}
	SATSolver::VarAssignment LingelingInterfacing::getAssignment(unsigned var){
		CALL("LingelingInterfacing::getAssignment(var)");
		ASS(_status == SATISFIABLE);
		int val;
		val = lglderef(_solver, var);
		switch (val){
		case -1 : return SATSolver::FALSE;
		case 1 : return SATSolver::TRUE;   
		case 0 : return SATSolver::DONT_CARE;
		default : ASSERTION_VIOLATION;
		}
	}


	void LingelingInterfacing::retractAllAssumptions(){
		CALL("LingelingInterfacing::retractAllAssumptions()");
		//in the case of Lingeling all the assumptions are valid only until the next lslsat/lglsimp
		//so we do not have to worry about retracting assumptions. 
		//but we still have to mark that at this point there are no more assumptions 

		_hasAssumptions = false;
		_assumptions->destroy();
	}

	bool LingelingInterfacing::hasAssumptions() const{
		CALL("LingelingInterfacing::hasAssumptions()");
		return _hasAssumptions;
	}

       /**
	*
	* A very basic implementation of getRefutation that uses all clauses
	* currently in the satSolver.
	*
	* @author Giles
	*/
	SATClause* LingelingInterfacing::getRefutation(){
		CALL("LingelingInterfacing::getRefutation");
		ASS(_status == SATSolver::UNSATISFIABLE);

		// Use *all* clauses in _addedClauses
		SATClauseList* prems = 0;
		SATClauseList::pushFromIterator(SATClauseStack::Iterator(_addedClauses),prems);
		SATInference* inf = new PropInference(prems);
		SATClause* dummy = new(0) SATClause(0);
		dummy->setInference(inf);

		return dummy;
	
	}

	void LingelingInterfacing::randomizeAssignment(){
		CALL("LingelingInterfacing::randomizeAssignment()");
		//here we should find a way to randomize the assignment
		
		//TODO - why do we want to do this?
		// We no longer randomize the assignment in SSplitter - this is not used
	}

	void LingelingInterfacing::printLingelingStatistics(){
		CALL("LingelingInterfacing::printLingelingStatistics");
		lglstats(_solver);
		cout<<"conflicts :" <<lglgetconfs(_solver)<<endl;
		cout<<"memory MB: "<<lglmb(_solver)<<endl;
		cout<<"memory Bytes: "<<lglbytes(_solver)<<endl;
		cout<<"seconds : "<<lglsec(_solver)<<endl;
		cout<<"processtime: "<<lglprocesstime()<<endl;

	}
	void LingelingInterfacing::testLingeling(){
		CALL("testLingleing");
		LGL * lgl = lglinit ();
		  int res;
		  lgladd (lgl, -14); lgladd (lgl, 2); lgladd (lgl, 0);  // binary clause
		  lgladd (lgl, 14); lgladd (lgl, -1); lgladd (lgl, 0);  // binary clause
		  lglassume (lgl, 1);                                   // assume '1'
		  lglfreeze (lgl, 1);                                   // will use '1' below
		  lglfreeze (lgl, 14);                                  // will use '14 too

		  ASS (lglfrozen (lgl, 1));
		  ASS (lglfrozen (lgl, 14));

		  res = lglsat (lgl);
		  ASS (res == 10);
		  (void) lglderef (lgl, 1);                             // fine
		  (void) lglderef (lgl, 2);                             // fine
		  (void) lglderef (lgl, 3);                             // fine !
		  (void) lglderef (lgl, 14);                            // fine
		  ASS (!lglusable (lgl, 2));
		  // lgladd (lgl, 2);                                   // ILLEGAL
		  // lglassume (lgl, 2);                                // ILLEGAL
		  ASS (lglusable (lgl, 15));				// '15' not used yet!
		  lgladd (lgl, -14); lgladd (lgl, 1); lgladd (lgl, 0);  // binary clause
		  lgladd (lgl, 15); lgladd (lgl, 0);                    // fine!
		  lglmelt (lgl, 14);                                    // '1' discarded
		  res = lglsat (lgl);
		  cout<<"second one \n";
		  ASS (res == 10);
		  ASS (lglfrozen (lgl, 1));
		  (void) lglderef (lgl, 1);                             // fine
		  (void) lglderef (lgl, 2);                             // fine
		  (void) lglderef (lgl, 3);                             // fine
		  (void) lglderef (lgl, 14);                            // fine
		  (void) lglderef (lgl, 15);                            // fine
		  ASS (!lglusable (lgl, 2));
		  ASS (!lglusable (lgl, 14));
		  // lglassume (lgl, 2);                                // ILLEGAL
		  // lglassume (lgl, 14);                               // ILLEGAL
		  lgladd (lgl, 1);   lgladd(lgl,0);                                   // still frozen
		  lglmelt (lgl, 1);
		  res = lglsat (lgl);
		  cout<<"third\n";
		  // none frozen
		  ASS (!lglusable (lgl, 1));
		  // lgladd(lgl, 1);                                    // ILLEGAL
		  lglsetopt (lgl, "plain", 1);				// disable BCE ...
		  lgladd (lgl, 8); lgladd (lgl, -9); lgladd (lgl, 0);
		  res = lglsat (lgl);
		  cout<<"patru\n";
		  ASS (res == 10);
		  ASS (!lglusable (lgl, 8));
		  ASS (!lglusable (lgl, -9));
		  ASS (lglreusable (lgl, 8));
		  ASS (lglreusable (lgl, -9));
		  lglreuse (lgl, 8);
		  lgladd (lgl, -8); lgladd (lgl, 0);
		  lglsetopt (lgl, "plain", 0);				// enable BCE ...
		  res = lglsat (lgl);
		  cout<<"cinci\n";
		  ASS (res);

	}
}; //end of the SAT namespace
