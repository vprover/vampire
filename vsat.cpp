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
#include "SAT/Preprocess.hpp"
#include "SAT/SingleWatchSAT.hpp"
#include "SAT/TWLSolver.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/CommandLine.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

using namespace Lib;
using namespace SAT;
using namespace Shell;
using namespace std;

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

void satSolverMode(const char* fname)
{
  CALL("satSolverMode");

  unsigned varCnt;
  SATClauseList* clauses = getPreprocessedClauses(fname, varCnt);

  cout<<"-start varcnt "<<varCnt<<"\n";

  TWLSolver ts(true);

  SATSolver::Status res;
  bool incremental = 1;
  if(incremental) {
    res = runSolverIncrementally(ts, varCnt, clauses);
  }
  else {
    res = runSolver(ts, varCnt, clauses);
  }

  switch(res) {
  case SATSolver::SATISFIABLE:
    cout<<"SATISFIABLE\n";
    break;
  case SATSolver::UNSATISFIABLE:
    cout<<"UNSATISFIABLE\n";
    break;
  case SATSolver::TIME_LIMIT:
    cout<<"TIME LIMIT\n";
    break;
  }

  clauses->destroy();
}

int main(int argc, char* argv [])
{
  CALL("main");

  System::registerArgv0(argv[0]);
  Random::setSeed(1);
  Options options;
  Allocator::setMemoryLimit(env.options->memoryLimit()*1048576);

  Lib::Random::setSeed(env.options->randomSeed());

  env.options->setTimeLimitInSeconds(3600);

  try {
    switch(argc) {
    case 1:
      satSolverMode(0);
      break;
    case 2:
      satSolverMode(argv[1]);
      break;
    default:
      cout<<"invalid parameter"<<endl;
      return 1;
    }
  } catch(MemoryLimitExceededException)
  {
    cerr<<"Memory limit exceeded\n";
    cout<<"-MEMORY_LIMIT\n";
  }

  env.statistics->print(cout);

  return 0;
}

