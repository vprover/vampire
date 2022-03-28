/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file tTwoVampires.cpp
 * Unit test checking it is possible to work two child Vampires at once
 */

#include "Lib/Portability.hpp"

#include "Test/UnitTesting.hpp"

#include <sstream>
#include <sys/wait.h>

#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Sys/SyncPipe.hpp"
#include "Lib/VString.hpp"

#include "Kernel/Problem.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Saturation/ProvingHelper.hpp"

#include "Parse/TPTP.hpp"

using namespace Lib;
using namespace Lib::Sys;
using namespace Kernel;
using namespace Saturation;
using namespace Shell;

//[[noreturn]] void runChild(UnitList* units, vstring slice);

void runChild(UnitList* units, vstring slice)
{
  CALL("runChild")
  
  int resultValue=1;
  try {    
    env.timer->reset();
    env.timer->start();
    TimeCounter::reinitialize();

    env.options->readFromEncodedOptions(slice);

    //To make sure the outputs of the two child Vampires don't interfere,
    //the pipe allows only one process at a time to possess the output for
    //writing (any other process that needs to output will wait).

    //However, not to block other processes from running, we claim the output
    //only when we actually need it -- this we announce it by calling the
    //functions env.beginOutput() and env.endOutput().

    //As outputs can happen all over the Vampire, every (non-debugging) output
    //is now encapsulated by a call to these two functions.

    //Also, to allow easy switching between cout and the pipe, the env.out
    //member has now become a function env.out().
    env.beginOutput();
    env.out()<<env.options->testId()<<" on "<<env.options->problemName()<<endl;
    env.endOutput();

    Problem prob(units);
    ProvingHelper::runVampire(prob, *env.options);

    //set return value to zero if we were successful
    if(env.statistics->terminationReason==Statistics::REFUTATION) {
      resultValue=0;
    }

    env.beginOutput();
    UIHelper::outputResult(env.out());
    env.endOutput();
  } 
  catch (Exception& exception) {        
    env.beginOutput();
    exception.cry(env.out());
    env.endOutput();
  } catch (std::bad_alloc& _) {    
    env.beginOutput();
    env.out() << "Insufficient system memory" << '\n';
    env.endOutput();
  }
  
  
  _exit(resultValue);
}

TEST_FUN(two_vampires1)
{
  //a non-trivial satisfiable problem (LCL354+1)
  vstring prob="fof(m1,axiom,( ! [P,Q,R,S] :( ( meets(P,Q) & meets(P,S) & meets(R,Q) ) => meets(R,S) ) ))."
      "fof(m2,axiom, ( ! [P,Q,R,S] : ( ( meets(P,Q) & meets(R,S) ) => ( ( meets(P,S) <~> ? [T] : "
      "  ( meets(P,T) & meets(T,S) ) ) <~> ? [T] : ( meets(R,T) & meets(T,Q) ) ) ) ))."
      "fof(m3,axiom, ( ! [P] : ? [Q,R] : ( meets(Q,P) & meets(P,R) ) ))."
      "fof(not_m5,axiom, ( ~ ( ! [P,Q] : ( meets(P,Q) => ? [R,S,T] : ( meets(R,P) & meets(Q,S) & meets(R,T) & meets(T,S) ) ) ) )).";

  //get the problem we'll be solving
  vistringstream inp(prob);
  UnitList* units=Parse::TPTP::parse(inp);

  //pipe for collecting the output from children
  SyncPipe childOutputPipe;

  //create the first child
  pid_t child1=Multiprocessing::instance()->fork();
  ASS_NEQ(child1,-1);
  if(!child1) {
    //we're in child1
    childOutputPipe.neverRead(); //we won't be reading from the pipe in children
    env.setPipeOutput(&childOutputPipe); //direct output into the pipe
      runChild(units, "dis+10_32_nwc=2.0:sac=on:spl=backtracking_20"); //start proving
  }

  pid_t child2=Multiprocessing::instance()->fork();
  ASS_NEQ(child2,-1);
  if(!child2) {
    //we're in child2
    childOutputPipe.neverRead();
    env.setPipeOutput(&childOutputPipe);
    runChild(units, "dis+4_8_30");
  }

  //We won't be writing anything into the pipe in the parent.
  //(We cannot call this function before the forks, as then
  //the children wouldn't be able to write either.)
  childOutputPipe.neverWrite();

  cout<<endl;

  childOutputPipe.acquireRead();  //start reading from the pipe
  vstring str;
  //We are processing the pipe until the EOF appears. This happens
  //when all the writing ends of the pipe are closed.
  //The closing is done either by calling the neverWrite() function,
  //destroying the SyncPipe object or terminating the process.
  while(!childOutputPipe.in().eof()) {
    getline(childOutputPipe.in(), str); //read line
    cout<<str<<endl; //and write it to the output
  }
  childOutputPipe.releaseRead(); //declare we have stopped reading from the pipe

  
  //retrieve the exit status of the first child
  int status;
  errno=0;
  pid_t res=waitpid(child1, &status, 0);
  if(res==-1) {
    SYSTEM_FAIL("Error in waiting for first forked process.",errno);
  }
  ASS_EQ(res,child1); //pid of the forked process and the one we waited for must be the same
  ASS(!WIFSTOPPED(status));
  ASS(!WIFEXITED(status) || WEXITSTATUS(status)!=0); //problem was satisfiable, so we shouldn't get zero

  //retrieve the exit status of the second child
  errno=0;
  pid_t res2=waitpid(child2, &status, 0);
  if(res2==-1) {
    SYSTEM_FAIL("Error in waiting for second forked process.",errno);
  }
  ASS_EQ(res2,child2); //pid of the forked process and the one we waited for must be the same
  ASS(!WIFSTOPPED(status));
  ASS(!WIFEXITED(status) || WEXITSTATUS(status)!=0); //problem was satisfiable, so we shouldn't get zero

}
