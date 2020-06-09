
/*
 * File Timer.cpp.
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
 * @file Timer.cpp
 * Implements class Timer.
 */

#include <ctime>
#include <unistd.h>
#include <sys/types.h>

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Environment.hpp"
#include "Int.hpp"
#include "Portability.hpp"
#include "System.hpp"
#include "TimeCounter.hpp"

#include "Shell/UIHelper.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Timer.hpp"

#define DEBUG_TIMER_CHANGES 0

using namespace std;
using namespace Lib;

bool Timer::s_timeLimitEnforcement = true;

#if UNIX_USE_SIGALRM

#include <cerrno>
#include <unistd.h>
#include <stdlib.h>
#include <signal.h>
#include <sys/time.h>
#include <sys/times.h>

#include "Lib/Sys/Multiprocessing.hpp"

#include "Shell/UIHelper.hpp"

int timer_sigalrm_counter=-1;

long Timer::s_ticksPerSec;
int Timer::s_initGuarantedMiliseconds;


void timeLimitReached()
{
  using namespace Shell;

  // CAREFUL, we might be in a signal handler and potentially at the same time inside Allocator which is not re-entrant
  // so any code below that allocates might corrupt the allocator state.
  // Therefore, the printing below should avoid allocations!

  env.beginOutput();
  reportSpiderStatus('t');
  if (outputAllowed()) {
    addCommentSignForSZS(env.out());
    env.out() << "Time limit reached!\n";

    if (UIHelper::portfolioParent) { // the boss
      addCommentSignForSZS(env.out());
      env.out() << "Proof not found in time ";
      Timer::printMSString(env.out(),env.timer->elapsedMilliseconds());
      env.out() << endl;

      if (szsOutputMode()) {
        env.out() << "% SZS status Timeout for "
                        << (env.options ? env.options->problemName().c_str() : "unknown") << endl;
      }
    } else // the actual child
      if (env.statistics) {
        env.statistics->print(env.out());
    }
  }
  env.endOutput();

  System::terminateImmediately(1);
}

void
timer_sigalrm_handler (int sig)
{
#if DEBUG_TIMER_CHANGES
  if(timer_sigalrm_counter<0) {
    cout << "Timer value became negative in timer_sigalrm_handler: " << timer_sigalrm_counter <<endl;
    System::terminateImmediately(1);
  }
#endif


  timer_sigalrm_counter++;

  if(Timer::s_timeLimitEnforcement && env.timeLimitReached()) {
    timeLimitReached();
  }

#if DEBUG_TIMER_CHANGES
  if(timer_sigalrm_counter<0) {
    cout << "Timer value became negative after increase: " << timer_sigalrm_counter <<endl;
    System::terminateImmediately(1);
  }
#endif

}

/** number of miliseconds (of CPU time) passed since some moment */
int Lib::Timer::miliseconds()
{
  CALL("Timer::miliseconds");
  ASS_GE(timer_sigalrm_counter, 0);

  return timer_sigalrm_counter;
}

int Lib::Timer::guaranteedMilliseconds()
{
  tms aux;
  clock_t ticks=times(&aux);
#if DEBUG_TIMER_CHANGES
  if(ticks==((clock_t)-1)) {
    cout << "clock value -1 returned by times()" <<endl;
    System::terminateImmediately(1);
  }
#endif
  if(ticks==((clock_t)-1)) {
    return -1;
  }
  return static_cast<long long>(ticks)*1000/s_ticksPerSec;
}

void Lib::Timer::suspendTimerBeforeFork()
{
  //if we use SIGALRM, we must disable it before forking and the restore it
  //afterwards (in both processes)
  itimerval tv1, tv2;
  tv1.it_value.tv_usec=0;
  tv1.it_value.tv_sec=0;
  tv1.it_interval.tv_usec=0;
  tv1.it_interval.tv_sec=0;
  errno=0;
  int res=setitimer(ITIMER_REAL, &tv1, &tv2);
  if(res!=0) {
    SYSTEM_FAIL("Call to setitimer failed when suspending timer.",errno);
  }
}

void Lib::Timer::restoreTimerAfterFork()
{
  itimerval tv1, tv2;
  tv2.it_interval.tv_usec = 1000;
  tv2.it_interval.tv_sec = 0;
  tv2.it_value.tv_usec = 1000;
  tv2.it_value.tv_sec = 0;
  errno=0;
  int res=setitimer(ITIMER_REAL, &tv2, &tv1);
  if(res!=0) {
    SYSTEM_FAIL("Call to setitimer failed when restoring timer.",errno);
  }
}

void Lib::Timer::ensureTimerInitialized()
{
  CALL("Timer::ensureTimerInitialized");

  if(timer_sigalrm_counter!=-1) {
    return;
  }

  timer_sigalrm_counter=0;

  signal (SIGALRM, timer_sigalrm_handler);
  struct itimerval oldt, newt;
  newt.it_interval.tv_usec = 1000;
  newt.it_interval.tv_sec = 0;
  newt.it_value.tv_usec = 1000;
  newt.it_value.tv_sec = 0;
  setitimer (ITIMER_REAL, &newt, &oldt);

  s_ticksPerSec=sysconf(_SC_CLK_TCK);
  s_initGuarantedMiliseconds=guaranteedMilliseconds();

  Sys::Multiprocessing::instance()->registerForkHandlers(suspendTimerBeforeFork, restoreTimerAfterFork, restoreTimerAfterFork);
}

void Lib::Timer::deinitializeTimer()
{
  CALL("Timer::deinitializeTimer");

  itimerval tv1, tv2;
  tv1.it_value.tv_usec=0;
  tv1.it_value.tv_sec=0;
  tv1.it_interval.tv_usec=0;
  tv1.it_interval.tv_sec=0;
  setitimer(ITIMER_REAL, &tv1, &tv2);
  
  signal (SIGALRM, SIG_IGN); // unregister the handler (and ignore the rest of SIGALRMs, should they still come) 
}

void Lib::Timer::syncClock()
{
  if(s_initGuarantedMiliseconds==-1) {
    //we're unable to sync clock as we weren't able to obtain number of ticks in the beginning
    bool reportedProblem = false;
    if(!reportedProblem) {
      reportedProblem = true;
      cerr << "cannot syncronize clock as times() initially returned -1" << endl;
    }
    return;
  }
  int newMilliseconds = guaranteedMilliseconds();
  if(newMilliseconds==-1) {
    //we're unable to sync clock as we cannot get the current time
    bool reportedProblem = false;
    if(!reportedProblem) {
      reportedProblem = true;
      cerr << "could not syncronize clock as times() returned -1" << endl;
    }
    return;
  }

  int newVal=newMilliseconds-s_initGuarantedMiliseconds;
  if(abs(newVal-timer_sigalrm_counter)>20) {
    timer_sigalrm_counter=newVal;
  }
}

void Lib::Timer::makeChildrenIncluded()
{
  //here are children always included as we measure the wall clock time
}

#else

#include <sys/time.h>
#include <sys/resource.h>

/** number of miliseconds (of CPU time) passed since some moment */
int Lib::Timer::miliseconds()
{
  struct timeval tim;
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  tim=ru.ru_utime;
  int t=tim.tv_sec*1000 + tim.tv_usec / 1000;
  tim=ru.ru_stime;
  t+=tim.tv_sec*1000 + tim.tv_usec / 1000;

  if(_mustIncludeChildren) {
    getrusage(RUSAGE_CHILDREN, &ru);
    tim=ru.ru_utime;
    t+=tim.tv_sec*1000 + tim.tv_usec / 1000;
    tim=ru.ru_stime;
    t+=tim.tv_sec*1000 + tim.tv_usec / 1000;
  }
  return t;
//  return (int)( ((long long)clock())*1000/CLOCKS_PER_SEC );
}

void Lib::Timer::syncClock()
{
}

void Lib::Timer::ensureTimerInitialized()
{
}

void Lib::Timer::deinitializeTimer()
{
}

void Lib::Timer::makeChildrenIncluded()
{
  CALL("Lib::Timer::makeChildrenIncluded");

  if(_mustIncludeChildren) {
    return;
  }

  if(_running) {
    struct timeval tim;
    struct rusage ru;
    getrusage(RUSAGE_CHILDREN, &ru);
    tim=ru.ru_utime;
    _start+=tim.tv_sec*1000 + tim.tv_usec / 1000;
    tim=ru.ru_stime;
    _start+=tim.tv_sec*1000 + tim.tv_usec / 1000;
  }
  _mustIncludeChildren=true;
}


#endif

namespace Lib
{

vstring Timer::msToSecondsString(int ms)
{
  return Int::toString(static_cast<float>(ms)/1000)+" s";
}

/**
 * Print string representing @b ms of milliseconds to @b str
 */
void Timer::printMSString(ostream& str, int ms)
{
  //having the call macro here distorts the stacks printouts
//  CALL("Timer::printMSString");

  if(ms<0) {
    str << '-';
    ms = -ms;
  }

  int sec=ms/1000;
  int msonly=ms%1000;
  if(sec) {
    str<<sec;
  }
  else {
    str<<'0';
  }
  str<<'.';
  if(msonly<100) {
    str<<'0';
    if(msonly<10) {
      str<<'0';
      if(!msonly) {
	str<<'0';
      }
    }
  }
  str<<msonly<<" s";
}

Timer* Timer::instance()
{
  static ScopedPtr<Timer> inst(new Timer());
  
  return inst.ptr();
}

};

//#include <iostream>
//
//int main (int argc, char* argv [])
//{
//  int counter = 0;
//  Lib::Timer timer;
//  int last = -1;
//  timer.start();
//
//  for (;;) {
//    counter++;
//    int current = timer.elapsedDeciseconds();
//    if (current <= last) {
//      continue;
//    }
//    last = current;
////      cout << current << "\n";
//    if (current == 100) {
//      cout << "Total calls to clock() during "
//	   << current
//	   << " deciseconds is "
//	   << counter
//	   << '\n';
//      return 0;
//    }
//  }
//}
//
