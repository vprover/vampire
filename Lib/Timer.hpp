/**
 *  @file Timer.hpp
 *  Defines class Timer
 *  @since 12/04/2006
 */

#ifndef __TIMER__
#define __TIMER__

#include <ctime>
#include "../Debug/Assertion.hpp"

using namespace std;

namespace Lib
{

/**
 * Class implementing timers. In 1 second of the user CPU time
 * one can do about 4M calls to clock() on my Samsung laptop
 * and about 3M calls on vampire.
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

    _elapsed += clock() - _start;
    _running = false;
  }

  /** Start the timer. Precondition: the timer must be running */
  inline void start()
  {
    ASS(! _running);

    _running = true;
    _start = clock();
  } // start

  /** elapsed time in seconds */
  int elapsedSeconds()
  {
    return elapsed() / CLOCKS_PER_SEC;
  }

  /** elapsed time in deciseconds */
  int elapsedDeciseconds()
  {
    long long time = elapsed();
    return (int)((time * 10) / CLOCKS_PER_SEC);
  }

  /** elapsed time in milliseconds */
  int elapsedMilliseconds()
  {
    long long time = elapsed();
    return (int)((time * 1000) / CLOCKS_PER_SEC);
  }

private:
  /** true if the timer is running */
  bool _running;
  /** last start time */
  clock_t _start;
  /** total elapsed time */
  clock_t _elapsed;

  /** elapsed time in ticks */
  inline clock_t elapsed()
  {
    return _running ? clock() - _start + _elapsed : _elapsed;
  }
}; // class Timer

} // namespace Lib

#endif
