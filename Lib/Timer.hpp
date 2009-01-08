/**
 *  @file Timer.hpp
 *  Defines class Timer
 *  @since 12/04/2006
 */

#ifndef __TIMER__
#define __TIMER__

#include <sys/time.h>
#include <sys/resource.h>

#include <ctime>
#include "../Debug/Assertion.hpp"

using namespace std;

namespace Lib
{

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

private:
  /** true if the timer is running */
  bool _running;
  /** last start time */
  int _start;
  /** total elapsed time */
  int _elapsed;

  /** number of miliseconds (of CPU time) passed since some moment */
  inline
  int miliseconds()
  {
    struct timeval tim;
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    tim=ru.ru_utime;
    int t=tim.tv_sec*1000 + tim.tv_usec / 1000;
    tim=ru.ru_stime;
    t+=tim.tv_sec*1000 + tim.tv_usec / 1000;
    return t;
//    return (int)( ((long long)clock())*1000/CLOCKS_PER_SEC );
  }



  /** elapsed time in ticks */
  inline
  int elapsed()
  {
    return _running ? miliseconds() - _start + _elapsed : _elapsed;
  }
}; // class Timer

} // namespace Lib

#endif
