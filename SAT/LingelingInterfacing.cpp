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
}
	LingelingInterfacing::LingelingInterfacing(const Options& opt, bool generateProofs) : 
		_generateProofs(generateProofs), _hasAssumptions(false){
			CALL("LingelingInterfacing::LingelingInterfacing");
			//here we should take care of all the options passed from the caller 
			Options _opts(opt);
			_solver = lglinit();

			//set the alarm handlers for sat solver
			lglseterm(_solver, checkalarm, &caughtalarm);
			sig_alrm_handler = signal (SIGALRM, catchlrm);

			//check how much time we spent already and set the maximum allowed for sat
			int current = env.timer->elapsedMilliseconds();
			int remaining = opt.timeLimitInDeciseconds()-current;
			if (remaining < 10)
				remaining = 10;
			alarm((remaining/10));

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
		addClausesToLingeling(clauseIterator);
	}

	void LingelingInterfacing::setSolverStatus(unsigned int status){
		CALL("LingelingInterfacing::setSolverStatus(uint status)");

		switch(status){
		case LGL_UNKNOWN : _status = SATSolver::UNKNOWN; break;
		case LGL_SATISFIABLE : _status = SATSolver::SATISFIABLE; break;
		case LGL_UNSATISFIABLE : _status = SATSolver::UNSATISFIABLE; break;
		default: ASSERTION_VIOLATION; break;
		}
	}

	void LingelingInterfacing::addClausesToLingeling(SATClauseIterator iterator){
		CALL("LingelingInterfacing::addClauses(SATClauseIterator iterator)");
		TimeCounter tc(TC_SAT_SOLVER);
		//iterate over all the clauses from the problem
		while(iterator.hasNext()){
			SATClause * currentClause = iterator.next();
			//treat each of the clauses individually. 
			unsigned clauseLength = currentClause->length();
			ASS_G(clauseLength, 1);

			for (unsigned idx = 0; idx < clauseLength ; idx++){
				//treat each of the literals individually 
				SATLiteral sLit = (*currentClause)[idx];
				unsigned currVar = sLit.var();
				ASS(lglusable(_solver, currVar));
				//in case our literal is with positive polarity
				if(sLit.polarity() == 1)
					lgladd(_solver, currVar);
				else 
					lgladd(_solver, -currVar);
				//TODO freezing of all the literals might not be a good idea!
				//why not reuse here instead of freezing the literals?
				lglfreeze(_solver, currVar);
			}
			//add the marker for clause termination 
			lgladd(_solver, 0);
		}

		unsigned int result = lglsat(_solver);
		setSolverStatus(result);

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
		_hasAssumptions = true;
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

	}

	bool LingelingInterfacing::hasAssumptions() const{
		CALL("LingelingInterfacing::hasAssumptions()");
		return _hasAssumptions;
	}

	SATClause* LingelingInterfacing::getRefutation(){
		CALL("LingelingInterfacing::getRefutation");
		testLingeling();
		USER_ERROR("not yet implemented");
		return 0;
	
	}

	void LingelingInterfacing::randomizeAssignment(){
		CALL("LingelingInterfacing::randomizeAssignment()");
		std::cout<<"randomize assignment";

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
