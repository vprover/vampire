
/*
 * File BFNTMainLoop.cpp.
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
/**
 * @file BFNTMainLoop.cpp
 * Implements class BFNTMainLoop.
 */

#include <cerrno>
#include <csignal>

#include "Lib/Portability.hpp"

#include <sys/types.h>
#include <sys/wait.h>

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/System.hpp"
#include "Lib/Timer.hpp"

#include "Lib/Sys/Multiprocessing.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/Property.hpp"
#include "Shell/TPTPPrinter.hpp"
#include "Shell/UIHelper.hpp"

#include "Statistics.hpp"

#include "BFNTMainLoop.hpp"

#define BFNT_CHILD_RESULT_SAT 0
#define BFNT_CHILD_RESULT_UNSAT 6
#define BFNT_CHILD_RESULT_UNKNOWN 7

namespace Shell
{

BFNTMainLoop::BFNTMainLoop(Problem& prb, const Options& opt)
: MainLoop(prb, opt),
  _childOpts(opt),
  _bfnt(prb.getProperty())
{
  CALL("BFNTMainLoop::BFNTMainLoop");

  //this is important, otherwise we'd start creating new and new processes
  // -- the child process would also run BFNT therefore also attemps to run
  //BFNT-running children.
  _childOpts.setBfnt(false);
}


void BFNTMainLoop::init()
{
  CALL("BFNTMainLoop::init");

  _hasSorts = _prb.getProperty()->hasNonDefaultSorts();
  if(_hasSorts) {
    return;
  }

  //Putting problem units into the BFNT convertor here may result into
  //one clause appearing in multiple Problem objects. In _prb and then in
  //child problems created by the spawed processes. Normally we wouldn't
  //want this to happen, but in the _prb object we do not use the clauses
  //any more after this point, and the child problems are isolated from each
  //other in different processes.
  _bfnt.apply(_prb.units());
}

/**
 * Run the child process that does proving on the flattenned problem
 *
 * Result statuses of the process:
 * BFNT_CHILD_RESULT_SAT
 * BFNT_CHILD_RESULT_UNSAT
 * BFNT_CHILD_RESULT_UNKNOWN
 */
void BFNTMainLoop::runChild(size_t modelSize)
{
  CALL("BFNTMainLoop::runChild");

  ScopedPtr<Problem> childPrb(_bfnt.createProblem(modelSize));

  ScopedPtr<MainLoop> childMainLoop(MainLoop::createFromOptions(*childPrb, _childOpts));
  MainLoopResult innerRes = childMainLoop->run();
  innerRes.updateStatistics();

  if(env.options->mode()!=Options::Mode::SPIDER) {
    if(innerRes.terminationReason==Statistics::SATISFIABLE || innerRes.terminationReason==Statistics::TIME_LIMIT) {
      env.beginOutput();
      env.statistics->print(env.out());
      env.endOutput();
    }
  }

  if(env.options->mode()!=Options::Mode::SPIDER && innerRes.terminationReason==Statistics::SATISFIABLE) {
    env.beginOutput();
    UIHelper::outputSatisfiableResult(env.out());
    env.endOutput();
    UIHelper::satisfiableStatusWasAlreadyOutput = true;
  }

  switch(innerRes.terminationReason) {
  case Statistics::SATISFIABLE:
    exit(BFNT_CHILD_RESULT_SAT);
  case Statistics::REFUTATION:
    exit(BFNT_CHILD_RESULT_UNSAT);
  default:
    exit(BFNT_CHILD_RESULT_UNKNOWN);
  }
  exit(BFNT_CHILD_RESULT_UNKNOWN);
}


MainLoopResult BFNTMainLoop::spawnChild(size_t modelSize)
{
  CALL("BFNTMainLoop::spawnChild");

  pid_t childPid=Multiprocessing::instance()->fork();

  if(!childPid) {
    runChild(modelSize);
    ASSERTION_VIOLATION;
  }


  System::ignoreSIGINT();

  int status;
  errno=0;
  pid_t res=waitpid(childPid, &status, 0);
  if(res==-1) {
    SYSTEM_FAIL("Error in waiting for forked process.",errno);
  }

  System::heedSIGINT();

  Timer::syncClock();

  if(res!=childPid) {
    INVALID_OPERATION("Invalid waitpid return value: "+Int::toString(res)+"  pid of forked Vampire: "+Int::toString(childPid));
  }

  ASS(!WIFSTOPPED(status));

  if( (WIFSIGNALED(status) && WTERMSIG(status)==SIGINT) ||
      (WIFEXITED(status) && WEXITSTATUS(status)==VAMP_RESULT_STATUS_SIGINT) )  {
    //if the forked Vampire was terminated by SIGINT (Ctrl+C), we also terminate
    //(3 is the return value for this case; see documentation for the
    //@b vampireReturnValue global variable)

    raise(SIGINT);
  }

  if(WIFEXITED(status)) {
    switch(WEXITSTATUS(status)) {
    case BFNT_CHILD_RESULT_SAT:
      UIHelper::satisfiableStatusWasAlreadyOutput = true;
      return MainLoopResult(Statistics::SATISFIABLE);
    case BFNT_CHILD_RESULT_UNSAT:
      return MainLoopResult(Statistics::REFUTATION);

    case VAMP_RESULT_STATUS_OTHER_SIGNAL:
    case VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION:
      INVALID_OPERATION("error in the child process");

    case BFNT_CHILD_RESULT_UNKNOWN:
    default: //under default will fall timeout
      return MainLoopResult(Statistics::UNKNOWN);
    }
  }
  else {
    return MainLoopResult(Statistics::UNKNOWN);
  }
}


MainLoopResult BFNTMainLoop::runImpl()
{
  CALL("BFNTMainLoop::runImpl");

  if(_hasSorts) {
    return MainLoopResult(Statistics::UNKNOWN);
  }


  env.timer->makeChildrenIncluded();

  size_t modelSize = 1;
  for(;;) {
    Timer::syncClock();
    if(env.timeLimitReached()) { return MainLoopResult(Statistics::TIME_LIMIT); }
    env.statistics->maxBFNTModelSize = modelSize;
    MainLoopResult childResult = spawnChild(modelSize);

    if(childResult.terminationReason == Statistics::SATISFIABLE) {
      return childResult;
    }

    modelSize++;
  }
}

}
