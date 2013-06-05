/**
 *  @file Timer.hpp
 *  Defines class Timer
 *  @since 12/04/2006
 */

#ifndef __Timer__
#define __Timer__

#include <string>
#include <iostream>

#include "Debug/Assertion.hpp"

#ifndef UNIX_USE_SIGALRM
//SIGALRM causes some problems with debugging
#define UNIX_USE_SIGALRM !VDEBUG
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
public:
  Timer(bool mustIncludeChildren=false) :
    _mustIncludeChildren(mustIncludeChildren),
    _running(false),
    _elapsed(0)
  { ensureTimerInitialized(); }

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

  /** Start the timer. Precondition: the timer must be running */
  inline void start()
  {
    ASS(! _running);

    _running = true;
    _start = miliseconds();
  } // start

  /**
   * Add to elapsed time. Useful when running a child process and adding
   * time spent by the parent to its elapsed time.
   * @since 05/06/2013 Vienna
   * @author Andrei Voronkov
   */
  inline void addToElapsedTime(int milliseconds)
  {
    if (_running) {
      _start -= milliseconds;
    }
    else {
      _elapsed += milliseconds;
    }
  } // addToElapsedTime

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
  static string msToSecondsString(int ms);
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
