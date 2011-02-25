#include <iostream>

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Random.hpp"
#include "Lib/Stack.hpp"
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

  Stack<SATClause*> cls;
  cls.loadFromIterator(SATClauseList::Iterator(clauses));

  solver.ensureVarCnt(varCnt);

  SATSolver::Status solverStatus = SATSolver::SATISFIABLE;

  while(cls.isNonEmpty()) {
    Stack<SATClause*> inner;
    unsigned currCnt= (cls.size()>1) ? (Random::getInteger(cls.size()-1)+1) : 1;
    while(currCnt--) {
      inner.push(cls.pop());
    }

    SATClauseIterator ic1=pvi( Stack<SATClause*>::Iterator(inner) );
    solver.addClauses(ic1);
    solverStatus = solver.getStatus();

    if(solverStatus!=SATSolver::SATISFIABLE) {
      return solverStatus;
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

  TWLSolver ts;

  SATSolver::Status res;
  bool incremental = 0;
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

#define INCREMENTAL_TEST 1

int main(int argc, char* argv [])
{
  CALL("main");

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

