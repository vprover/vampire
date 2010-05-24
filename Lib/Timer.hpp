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
  Timer() :
    _running(false),
    _elapsed(0)
  {}

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

  static void initTimer();
  static string msToSecondsString(int ms);
  static void printMSString(ostream& str, int ms);
private:
  /** true if the timer is running */
  bool _running;
  /** last start time */
  int _start;
  /** total elapsed time */
  int _elapsed;

  int miliseconds();



  /** elapsed time in ticks */
  inline
  int elapsed()
  {
    return _running ? miliseconds() - _start + _elapsed : _elapsed;
  }
}; // class Timer

} // namespace Lib

#endif /* __Timer__ */
