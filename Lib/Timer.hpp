
/*
 * File Timer.hpp.
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
 *  @file Timer.hpp
 *  Defines class Timer
 *  @since 12/04/2006
 */

#ifndef __Timer__
#define __Timer__

#include <iostream>

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"               // to declare checked_delete a fried for ScopedPtr's destruction to work
#include "Allocator.hpp"
#include "VString.hpp"

#ifndef UNIX_USE_SIGALRM
//SIGALRM causes some problems with debugging
//[one problem might have been removed, so it's worth checking if the demand for UNIX_USE_SIGALRM in VDEBUG arises]
#define UNIX_USE_SIGALRM 1 // MS: only the UNIX_USE_SIGALRM seems to be working currently (experiment with SMTCOMP mode); the problem with debugging under UNIX_USE_SIGALRM might have really gone, so let's try
#endif

//we don't need SIGALRM in Api, and it causes problems debugging
#ifdef VAPI_LIBRARY
#if VAPI_LIBRARY

#undef UNIX_USE_SIGALRM
#define UNIX_USE_SIGALRM 0

#endif
#endif

namespace Lib
{

using namespace std;

/**
 * Class implementing timers.
 * @since 12/04/2006 Bellevue
 */
class Timer
{
  Timer(bool mustIncludeChildren=false)
    :
    _mustIncludeChildren(mustIncludeChildren),
    _running(false),
    _elapsed(0)
  { (void)_mustIncludeChildren; // MS: to get it of the unused private field warning when UNIX_USE_SIGALRM
    ensureTimerInitialized(); }

  ~Timer() { deinitializeTimer(); }
  friend void ::checked_delete<Timer>(Timer*);
  
public:
  CLASS_NAME(Timer);
  USE_ALLOCATOR(Timer);

  static Timer* instance();
  
  /** stop the timer and reset the clock */
  inline void reset()
  { _running = false;
    _elapsed = 0; }

  /** Stop the timer. Precondition: the timer must be running */
  inline void stop()
  {
    ASS(_running);

    _elapsed += miliseconds() - _start;
    _running = false;
  }

  /** Start the timer. Precondition: the timer must not be running */
  inline void start()
  {
    ASS(! _running);

    _running = true;
    _start = miliseconds();
  } // start

  /** elapsed time in seconds */
  int elapsedSeconds()
  {
    return elapsed()/1000;
  }

  /** elapsed time in deciseconds */
  int elapsedDeciseconds()
  {
    return elapsed()/100;
  }

  /** elapsed time in milliseconds */
  int elapsedMilliseconds()
  {
    return elapsed();
  }

  void makeChildrenIncluded();

  static void ensureTimerInitialized();
  static void deinitializeTimer();
  static vstring msToSecondsString(int ms);
  static void printMSString(ostream& str, int ms);

  static void setTimeLimitEnforcement(bool enabled)
  { s_timeLimitEnforcement = enabled; }

  static void syncClock();

  static bool s_timeLimitEnforcement;
private:
  /** true if the timer must account for the time spent in
   * children (otherwise it may or may not) */
  bool _mustIncludeChildren;
  /** true if the timer is running */
  bool _running;
  /** last start time */
  int _start;
  /** total elapsed time */
  int _elapsed;

  int miliseconds();

#if UNIX_USE_SIGALRM
  static void suspendTimerBeforeFork();
  static void restoreTimerAfterFork();

  static int guaranteedMilliseconds();

  static long s_ticksPerSec;
  static int s_initGuarantedMiliseconds;
#endif

  /** elapsed time in ticks */
  inline
  int elapsed()
  {
    return _running ? miliseconds() - _start + _elapsed : _elapsed;
  }
}; // class Timer

} // namespace Lib

#endif /* __Timer__ */
