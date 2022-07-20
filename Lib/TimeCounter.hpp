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
 * @file TimeCounter.hpp
 * Defines class TimeCounter.
 */


#ifndef __TimeCounter__
#define __TimeCounter__

#include "Shell/TimeTracing.hpp"

#define TC_LITERAL_ORDER_AFTERCHECK "literal order aftercheck"
#define TC_CONDENSATION "condensation"
#define TC_PARSING "parsing"
#define TC_PREPROCESSING "preprocessing"
#define TC_TERM_SHARING "term sharing"

#include <ostream>

namespace Lib {

using namespace std;

enum TimeCounterUnit
{
  TC_OTHER,
  __TC_ELEMENT_COUNT,
  __TC_NONE
};

class TimeCounter
{
public:
  inline TimeCounter(TimeCounterUnit tcu)
  {
    if(!s_measuring) return;
    startMeasuring(tcu);
  }
  inline ~TimeCounter()
  {
    if(!s_measuring) return;
    stopMeasuring();
  }

  static void printReport(ostream& out);


  /**
   * Stop time measuring. If not called, time measuring is
   * stopped in the destructor.
   */
  void stop()
  {
    if(!s_measuring) return;
    stopMeasuring();
    _tcu=__TC_NONE; //so that nothing happens when we call stopMeasuring() in destructor
  }

  static bool isBeingMeasured(TimeCounterUnit tcu)
  {
    return s_measureInitTimes[tcu]!=-1;
  }

  static void reinitialize();

private:
  void startMeasuring(TimeCounterUnit tcu);
  void stopMeasuring();

  static void initialize();
  static void outputSingleStat(TimeCounterUnit tcu, ostream& out);

  /**
   * Record measurements of all timers currently running,
   * so that this data is reflected in a subsequent report.
   */
  static void snapShot();

  TimeCounterUnit _tcu;

  /**
   * Current top level counter.
   *
   * The currently passing time contribute's to this counter's "own" time.
   */
  static TimeCounter* s_currTop;

  /**
   * To store s_currTop when (*this) becomes the new top.
   */
  TimeCounter* previousTop;

  /**
   * Determines whether the time measurement will be performed.
   *
   * Initially is set to @b true, and the first time the measurement is requested,
   * the env.options structure is checked, whether measurement should indeed be done,
   * and if not, it is set to @b false.
   */
  static bool s_measuring;
  /**
   * Contains true if the @b s_measuredTimes and @b s_measureInitTimes arrays
   * have been initialized.
   */
  static bool s_initialized;
  /**
   * Contains number of milliseconds passed in each TimeCounterUnit.
   */
  static int s_measuredTimes[];
  /**
   * Contains number of milliseconds passed in each TimeCounterUnit's children.
   *
   * "ownTime" = "measuredTime" - "measuredTimesChildren"
   */
  static int s_measuredTimesChildren[];
  /**
   * For each TimeCounterUnit contains either -1 if the unit is not being
   * measured, or a non-negative number representing initial time of the current
   * block in the unit.
   */
  static int s_measureInitTimes[];
};

};

#endif /* __TimeCounter__ */
