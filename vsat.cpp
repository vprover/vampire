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

void runIncrementallyOnFile(const char* fname)
{
  unsigned maxVar;
  SATClauseIterator cit=Preprocess::removeDuplicateLiterals( DIMACS::parse(fname, maxVar) );
  unsigned varCnt=maxVar+1;

  Stack<SATClause*> cls;
  cls.loadFromIterator(cit);


  cout<<"-start varcnt "<<varCnt<<"\n";

  TWLSolver ts;
  ts.ensureVarCnt(varCnt);

  while(cls.isNonEmpty()) {
    Stack<SATClause*> inner;
    unsigned currCnt= (cls.size()>1) ? (Random::getInteger(cls.size()-1)+1) : 1;
    while(currCnt--) {
      inner.push(cls.pop());
    }

    SATClauseIterator ic1=pvi( Stack<SATClause*>::Iterator(inner) );
    ts.addClauses(ic1);

    if(ts.getStatus()==TWLSolver::UNSATISFIABLE) {
      cout<<"-UNSATISFIABLE\n";
      return;
    }
  }


  if(ts.getStatus()==TWLSolver::SATISFIABLE) {
    cout<<"-SATISFIABLE\n";
  }
}

void runOnFile(const char* fname)
{
  unsigned maxVar;
  SATClauseIterator cit=Preprocess::removeDuplicateLiterals( DIMACS::parse(fname, maxVar) );
  unsigned varCnt=maxVar+1;

  Stack<SATClause*> cls;
  cls.loadFromIterator(cit);

  SATClauseIterator ic1=pvi( Stack<SATClause*>::Iterator(cls) );

  cout<<"-start varcnt "<<varCnt<<"\n";

  TWLSolver ts;
  ts.ensureVarCnt(varCnt);
  ts.addClauses(ic1);

  if(ts.getStatus()==TWLSolver::SATISFIABLE) {
    cout<<"-SATISFIABLE\n";
  }
  if(ts.getStatus()==TWLSolver::UNSATISFIABLE) {
    cout<<"-UNSATISFIABLE\n";
  }
}

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
    runOnFile(0);
//      runIncrementallyOnFile(0);
      break;
    case 2:
    runOnFile(argv[1]);
//      runIncrementallyOnFile(argv[1]);
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

  return 0;
}

