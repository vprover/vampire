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
  string fileName;

  SatOptions()
  : simulateIncremental(false),
    minimizingSolver(false),
    checkingSolver(false)
  {}
};



SATClauseList* getInputClauses(const char* fname, unsigned& varCnt)
{
  CALL("getInputClauses");

  unsigned maxVar;
  SATClauseIterator cit=Preprocess::removeDuplicateLiterals( DIMACS::parse(fname, maxVar) );
  varCnt=maxVar+1;

  SATClauseList* clauses = 0;
  SATClauseList::pushFromIterator(cit, clauses);
  return clauses;
}

void preprocessClauses(unsigned varCnt, SATClauseList*& clauses)
{
  CALL("getInputClauses");

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
      solver.retractAllAssumptions();

      SATClauseStack::Iterator uit(units);
      while(uit.hasNext()) {
	SATClause* cl = uit.next();
	solver.addAssumption((*cl)[0]);

	solverStatus = solver.getStatus();
	if(solverStatus!=SATSolver::SATISFIABLE) { return solverStatus; }
      }
      solver.retractAllAssumptions();
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

  solver.ensureVarCnt(varCnt);
  solver.addClauses(pvi( SATClauseList::Iterator(clauses)));
  return solver.getStatus();
}

void satSolverMode(SatOptions& opts)
{
  CALL("satSolverMode");

  env.statistics->phase = Statistics::PARSING;
  unsigned varCnt;
  SATClauseList* clauses;
  if(opts.fileName.empty()) {
    clauses = getPreprocessedClauses(0, varCnt);
  }
  else {
    clauses = getPreprocessedClauses(opts.fileName.c_str(), varCnt);
  }

  env.statistics->phase = Statistics::SATURATION;

  cout<<"-start varcnt "<<varCnt<<"\n";

  SATSolverSCP solver(new TWLSolver(*env.options, true));

  if(opts.minimizingSolver) {
    solver = new MinimizingSolver(solver.release());
  }
  if(opts.checkingSolver) {
    solver = new CheckedSatSolver(solver.release());
  }

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
    break;
  case SATSolver::UNSATISFIABLE:
    cout<<"UNSATISFIABLE\n";
    break;
  default:
    ASSERTION_VIOLATION;
  }

  clauses->destroy();
}

void processArgs(StringStack& args, SatOptions& opts)
{
  CALL("processArgs");

  StringStack::StableDelIterator it(args);
  while(it.hasNext()) {
    string arg = it.next();
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
      string traceStr(it.next());
      it.del();
      PROCESS_TRACE_SPEC_STRING(traceStr);
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
}

int main(int argc, char* argv [])
{
  CALL("main");

  try {
    System::registerArgv0(argv[0]);
    Random::setSeed(1);
    Options options;
    Allocator::setMemoryLimit(env.options->memoryLimit()*1048576);

    StringStack args;
    System::readCmdArgs(argc, argv, args);

    SatOptions opts;
    processArgs(args, opts);

    Lib::Random::setSeed(env.options->randomSeed());

    env.options->setTimeLimitInSeconds(3600);

    satSolverMode(opts);
  }
  catch(MemoryLimitExceededException&)
  {
    cerr<<"Memory limit exceeded\n";
    cout<<"-MEMORY_LIMIT\n";
  }
  catch(TimeLimitExceededException&)
  {
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

