/**
 * @file BFNTMainLoop.cpp
 * Implements class BFNTMainLoop.
 */

#include <cerrno>
#include <csignal>

#if !COMPILER_MSVC

#include <sys/types.h>
#include <sys/wait.h>

#endif


#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/System.hpp"
#include "Lib/Timer.hpp"

#include "Lib/Sys/Multiprocessing.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"

#include "BFNTMainLoop.hpp"

#undef LOGGING
#define LOGGING 1

#define BFNT_CHILD_RESULT_SAT 0
#define BFNT_CHILD_RESULT_UNSAT 1
#define BFNT_CHILD_RESULT_UNKNOWN 2

namespace Kernel
{

void BFNTMainLoop::addInputClauses(ClauseIterator cit)
{
  CALL("BFNTMainLoop::addInputClauses");

  UnitList* units = 0;
  UnitList::pushFromIterator(getStaticCastIterator<Unit*>(cit), units);

  _bfnt.apply(units);

  units->destroy();
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

  UnitList* units = _bfnt.create(modelSize);
  ClauseIterator cit = pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(units)) );

#if LOGGING
  UnitList::Iterator puit(units);
  while(puit.hasNext()) {
    Unit* u = puit.next();
    LOG("Flattenned unit: "<<u->toString());
  }
#endif


  _inner->addInputClauses(cit);
  MainLoopResult innerRes = _inner->run();

  LOG("Child termination reason: "
      << ((innerRes.terminationReason==Statistics::SATISFIABLE) ? "Satisfiable" :
	  (innerRes.terminationReason==Statistics::REFUTATION) ? "Unsatisfiable" : "Unknown") );
#if LOGGING
  if(env.statistics->model!="") {
    LOG("Model: "<<endl<<env.statistics->model);
  }
#endif

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
      return MainLoopResult(Statistics::SATISFIABLE);
    case BFNT_CHILD_RESULT_UNSAT:
      return MainLoopResult(Statistics::REFUTATION);
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

  size_t modelSize = 1;
  for(;;) {
    Timer::syncClock();
    if(env.timeLimitReached()) { return MainLoopResult(Statistics::TIME_LIMIT); }
    LOG("Trying model size "<<modelSize);
    MainLoopResult childResult = spawnChild(modelSize);

    if(childResult.terminationReason == Statistics::SATISFIABLE) {
      return childResult;
    }

    modelSize++;
  }
}


}
