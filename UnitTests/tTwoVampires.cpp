/**
 * @file tTwoVampires.cpp
 * Unit test checking it is possible to work two child Vampires at once
 */

#include "Lib/Portability.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID two_vampires
UT_CREATE;


//forking isn't supported in the visual studio
#if !COMPILER_MSVC

#include <string>
#include <sstream>
#include <sys/wait.h>

#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Sys/SyncPipe.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTPParser.hpp"
#include "Shell/UIHelper.hpp"

using namespace Lib;
using namespace Lib::Sys;
using namespace Kernel;
using namespace Shell;

void runChild(UnitList* units, string slice) __attribute__((noreturn));

void runChild(UnitList* units, string slice)
{
  int resultValue=1;
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();

  env.options->readFromTestId(slice);

  env.beginOutput();
  env.out()<<env.options->testId()<<" on "<<env.options->problemName()<<endl;
  env.endOutput();

  UIHelper::runVampire(units);

  //set return value to zero if we were successful
  if(env.statistics->terminationReason==Statistics::REFUTATION) {
    resultValue=0;
  }

  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

  exit(resultValue);
}

TEST_FUN(two_vampires1)
{
  //a non-trivial satisfiable problem (LCL354+1)
  string prob="fof(m1,axiom,( ! [P,Q,R,S] :( ( meets(P,Q) & meets(P,S) & meets(R,Q) ) => meets(R,S) ) ))."
      "fof(m2,axiom, ( ! [P,Q,R,S] : ( ( meets(P,Q) & meets(R,S) ) => ( ( meets(P,S) <~> ? [T] : "
      "  ( meets(P,T) & meets(T,S) ) ) <~> ? [T] : ( meets(R,T) & meets(T,Q) ) ) ) ))."
      "fof(m3,axiom, ( ! [P] : ? [Q,R] : ( meets(Q,P) & meets(P,R) ) ))."
      "fof(not_m5,axiom, ( ~ ( ! [P,Q] : ( meets(P,Q) => ? [R,S,T] : ( meets(R,P) & meets(Q,S) & meets(R,T) & meets(T,S) ) ) ) )).";

  stringstream inp(prob);
  TPTPLexer lex(inp);
  TPTPParser par(lex);
  UnitList* units=par.units();

  SyncPipe childOutputPipe;

  pid_t child1=Multiprocessing::instance()->fork();
  ASS_NEQ(child1,-1);
  if(!child1) {
    //we're in child1
    childOutputPipe.neverRead();
    env.setPipeOutput(&childOutputPipe);
    runChild(units, "dis+10_32_nwc=2.0:sac=on:spl=backtracking_20");
  }

  pid_t child2=Multiprocessing::instance()->fork();
  ASS_NEQ(child2,-1);
  if(!child2) {
    //we're in child1
    childOutputPipe.neverRead();
    env.setPipeOutput(&childOutputPipe);
    runChild(units, "dis+4_8_30");
  }

  childOutputPipe.neverWrite();

  cout<<endl;

  childOutputPipe.acquireRead();
  string str;
  while(!childOutputPipe.in().eof()) {
    getline(childOutputPipe.in(), str);
    cout<<str<<endl;
  }
  childOutputPipe.releaseRead();


  int status;
  errno=0;
  pid_t res=waitpid(child1, &status, 0);
  if(res==-1) {
    SYSTEM_FAIL("Error in waiting for first forked process.",errno);
  }
  ASS_EQ(res,child1); //pid of the forked process and the one we waited for must be the same
  ASS(!WIFSTOPPED(status));
  ASS(!WIFEXITED(status) || WEXITSTATUS(status)!=0); //problem was satisfiable, so we shouldn't get zero

  errno=0;
  pid_t res2=waitpid(child2, &status, 0);
  if(res2==-1) {
    SYSTEM_FAIL("Error in waiting for second forked process.",errno);
  }
  ASS_EQ(res2,child2); //pid of the forked process and the one we waited for must be the same
  ASS(!WIFSTOPPED(status));
  ASS(!WIFEXITED(status) || WEXITSTATUS(status)!=0); //problem was satisfiable, so we shouldn't get zero

}

#endif
