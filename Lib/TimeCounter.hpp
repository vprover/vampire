/**
 * @file TimeCounter.hpp
 * Defines class TimeCounter.
 */


#ifndef __TimeCounter__
#define __TimeCounter__

namespace Lib {

enum TimeCounterUnit
{
  TC_PARSING,
  TC_PREPROCESSING,
  TC_BDD,
  TC_SIMPLIFYING_UNIT_LITERAL_INDEX_MAINTENANCE,
  TC_FORWARD_SUBSUMPTION_INDEX_MAINTENANCE,
  TC_BINARY_RESOLUTION_INDEX_MAINTENANCE,
  TC_BACKWARD_SUBSUMPTION_INDEX_MAINTENANCE,
  TC_BACKWARD_SUPERPOSITION_INDEX_MAINTENANCE,
  TC_FORWARD_SUPERPOSITION_INDEX_MAINTENANCE,
  TC_BACKWARD_DEMODULATION_INDEX_MAINTENANCE,
  TC_FORWARD_DEMODULATION_INDEX_MAINTENANCE,
  TC_SPLITTING_COMPONENT_INDEX_MAINTENANCE,
  TC_FORWARD_SUBSUMPTION,
  TC_BACKWARD_SUBSUMPTION,
  TC_FORWARD_DEMODULATION,
  TC_BACKWARD_DEMODULATION,
  TC_RESOLUTION,
  TC_SUPERPOSITION,
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

  static void printReport();

private:
  void startMeasuring(TimeCounterUnit tcu);
  void stopMeasuring();

  static void initialize();
  static void printSingleStat(TimeCounterUnit tcu);


  TimeCounterUnit _tcu;


  /**
   * Determines whether the time measurement will be performed.
   *
   * Initially is set to @b true, and the first time the measurement is requested,
   * the env.options structure is checked, whether measurement should indeed be done,
   * and if not, it is set to @b false.
   */
  static bool s_measuring;
  /**
   * Contaings true if the @b s_measuredTimes and @b s_measureInitTimes arrays
   * have been initialized.
   */
  static bool s_initialized;
  /**
   * Contains number of miliseconds passed in each TimeCounterUnit.
   */
  static int s_measuredTimes[];
  /**
   * For each TimeCounterUnit contains either -1 if the unit is not being
   * measured, or a non-negative number representing initial time of the current
   * block in the unit.
   */
  static int s_measureInitTimes[];

  static int s_measuredCnt;
};

};

#endif /* __TimeCounter__ */
