
/*
 * File vsat.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
#include <iostream>

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Random.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"
#include "Lib/Timer.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/Int.hpp"

#include "SAT/DIMACS.hpp"
#include "SAT/MinimizingSolver.hpp"
#include "SAT/Preprocess.hpp"
#include "SAT/SingleWatchSAT.hpp"
#include "SAT/TWLSolver.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/CommandLine.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Test/CheckedSatSolver.hpp"

using namespace Lib;
using namespace SAT;
using namespace Shell;
using namespace Test;
using namespace std;

struct SatOptions
{
  bool simulateIncremental;
  bool minimizingSolver;
  bool checkingSolver;
  vstring fileName;

  SatOptions()
  : simulateIncremental(false),
    minimizingSolver(false),
    checkingSolver(false)
  {}
};



SATClauseList* getInputClauses(const char* fname, unsigned& varCnt)
{
  CALL("getInputClauses");

  SATClauseIterator cit=Preprocess::removeDuplicateLiterals( DIMACS::parse(fname, varCnt) );

  SATClauseList* clauses = 0;
  SATClauseList::pushFromIterator(cit, clauses);
  return clauses;
}

void preprocessClauses(unsigned varCnt, SATClauseList*& clauses)
{
  CALL("preprocessClauses");

  Preprocess::filterPureLiterals(varCnt, clauses);
//  SATClauseIterator cl = pvi( SATClauseList::DestructiveIterator(clauses));
//  SATClauseIterator units, nonUnits;
//  Preprocess::propagateUnits(cl, units, nonUnits);
//  clauses = 0;
//  SATClauseList::pushFromIterator(nonUnits, clauses);
}

SATClauseList* getPreprocessedClauses(const char* fname, unsigned& varCnt)
{
  CALL("getPreprocessedClauses");

  SATClauseList* clauses = getInputClauses(fname, varCnt);
  preprocessClauses(varCnt, clauses);
  return clauses;
}


SATSolver::Status runSolverIncrementally(SATSolver& solver, unsigned varCnt, SATClauseList* clauses)
{
  CALL("runSolverIncrementally");

  bool testAssumptions = true;

  Stack<SATClause*> cls;
  cls.loadFromIterator(SATClauseList::Iterator(clauses));

  solver.ensureVarCnt(varCnt);

  SATSolver::Status solverStatus = SATSolver::SATISFIABLE;

  SATClauseStack units;
  SATClauseStack inner;

  while(cls.isNonEmpty()) {
    units.reset();
    inner.reset();
    unsigned currCnt= (cls.size()>1) ? (Random::getInteger(cls.size()-1)+1) : 1;
    while(currCnt--) {
      SATClause* cl = cls.pop();
      if(cl->length()==1) {
	units.push(cl);
      }
      else {
	inner.push(cl);
      }
    }

    SATClauseIterator ic1=pvi( Stack<SATClause*>::Iterator(inner) );
    solver.addClauses(ic1);

    solverStatus = solver.getStatus();
    if(solverStatus!=SATSolver::SATISFIABLE) {
      return solverStatus;
    }

    if(testAssumptions) {

      //first we try adding wrong literals, so that we check retracting works as it should...
      SATClauseStack::Iterator uit0(units);
      while(uit0.hasNext()) {
	SATClause* cl = uit0.next();
	solver.addAssumption((*cl)[0].opposite());
      }
      //solver.retractAllAssumptions();

      SATClauseStack::Iterator uit(units);
      while(uit.hasNext()) {
	SATClause* cl = uit.next();
	solver.addAssumption((*cl)[0]);

	solverStatus = solver.getStatus();
	if(solverStatus!=SATSolver::SATISFIABLE) { return solverStatus; }
      }
      //solver.retractAllAssumptions();
    }

    while(units.isNonEmpty()) {
      SATClause* cl = units.pop();
      solver.addClauses(pvi( getSingletonIterator(cl) ));

      ASS_EQ(solver.getStatus(), SATSolver::SATISFIABLE);
    }
  }

  ASS_EQ(solverStatus, SATSolver::SATISFIABLE);
  return SATSolver::SATISFIABLE;
}


SATSolver::Status runSolver(SATSolver& solver, unsigned varCnt, SATClauseList* clauses)
{
  CALL("runSolver");

  /*solver.ensureVarCnt(varCnt);
  solver.addClauses(pvi( SATClauseList::Iterator(clauses)));
  return solver.getStatus();
  */
  solver.addClauses(pvi(SATClauseList::Iterator(clauses)));
  return solver.getStatus();
}

void satSolverMode(SatOptions& opts)
{
	CALL("satSolverMode");

  env.statistics->phase = Statistics::PARSING;
  unsigned varCnt;
  SATClauseList* clauses;

  if(opts.fileName.empty()) {
	  clauses = getInputClauses(0,varCnt);
	  //clauses = getPreprocessedClauses(0, varCnt);
  }
  else {
	  clauses = getInputClauses(opts.fileName.c_str(), varCnt);
    //clauses = getPreprocessedClauses(opts.fileName.c_str(), varCnt);
  }

  env.statistics->phase = Statistics::SAT_SOLVING;

  cout<<"start varcnt :"<<varCnt<<"\n";

  SATSolverSCP solver(new TWLSolver(*env.options, true));
  //for the minimized case
  //solver = new MinimizingSolver(solver.release());

  /*if(opts.minimizingSolver) {
    solver = new MinimizingSolver(solver.release());
  }
  if(opts.checkingSolver) {
    solver = new CheckedSatSolver(solver.release());
  }
  */

  SATSolver::Status res;
  if(opts.simulateIncremental) {
    res = runSolverIncrementally(*solver, varCnt, clauses);
  }
  else {
    res = runSolver(*solver, varCnt, clauses);
  }

  env.statistics->phase = Statistics::FINALIZATION;

  switch(res) {
  case SATSolver::SATISFIABLE:
    cout<<"SATISFIABLE\n";
    env.statistics->terminationReason = Statistics::SATISFIABLE;
    break;
  case SATSolver::UNSATISFIABLE:
    cout<<"UNSATISFIABLE\n";
    env.statistics->terminationReason = Statistics::REFUTATION;
    break;
  case SATSolver::UNKNOWN:
    cout<<"Unknown\n";
    break;
  default:
    cout<<res<<endl;
    ASSERTION_VIOLATION;
  }

  //clauses->destroy();
}

bool processArgs(StringStack& args, SatOptions& opts)
{
  CALL("processArgs");
  bool flag=true;
  StringStack::StableDelIterator it(args);
  while(it.hasNext()) {
    vstring arg = it.next();
    if(arg=="-incr") {
      opts.simulateIncremental = true;
      it.del();
    }
    else if(arg=="-minim") {
      opts.minimizingSolver = true;
      it.del();
    }
    else if(arg=="-checked") {
      opts.checkingSolver = true;
      it.del();
    }
    else if(arg=="-tr") {
      it.del();
      if(!it.hasNext()) {
	USER_ERROR("value for -tr option expected");
      }
      vstring traceStr(it.next());
      it.del();
      PROCESS_TRACE_SPEC_STRING(traceStr);
    }
    else if(arg == "-t"){
    	it.del();
    	if(!it.hasNext()){
    		USER_ERROR("value for -t option expected");
    	}
    	vstring timelimit(it.next());
    	it.del();
    	int timeout;
    	Lib::Int::stringToInt(timelimit, timeout);

    	env.options->setTimeLimitInSeconds(timeout);
    	flag=false;
    }
  }
  if(args.size()>1) {
    while(args.isNonEmpty()) {
      cout<<args.pop()<<endl;
    }
    USER_ERROR("too many arguments");
  }
  if(args.isNonEmpty()) {
    opts.fileName = args.pop();
  }
  return flag;
}

int main(int argc, char* argv [])
{
  CALL("main");
  //ScopedPtr<SATSolver> solver;
 
  try {
    System::registerArgv0(argv[0]);
    Random::setSeed(1);
    Options options;
    Allocator::setMemoryLimit(env.options->memoryLimit()*1048576);

    StringStack args;
    System::readCmdArgs(argc, argv, args);

    SatOptions opts;
    if (processArgs(args, opts)){
    	env.options->setTimeLimitInDeciseconds(3600);
    	}

    Lib::Random::setSeed(env.options->randomSeed());

    satSolverMode(opts);
  }
  catch(MemoryLimitExceededException&)
  {
    cerr<<"Memory limit exceeded\n";
    env.statistics->terminationReason = Statistics::MEMORY_LIMIT;
    cout<<"-MEMORY_LIMIT\n";
  }
  catch(TimeLimitExceededException&)
  {
    env.statistics->terminationReason = Statistics::TIME_LIMIT;
    cout<<"TIME LIMIT\n";
  }
  catch(UserErrorException& e)
  {

    cout<<"USER ERROR: ";
    e.cry(cout);
    cout<<"\n";
  }

  env.statistics->print(cout);

  return 0;
}

