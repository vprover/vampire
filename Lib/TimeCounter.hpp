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

#include <ostream>

namespace Lib {

using namespace std;

enum TimeCounterUnit
{
  TC_RAND_OPT,
  TC_PARSING,
  TC_PROPERTY_EVALUATION,
  TC_PREPROCESSING,
  TC_BCE,
  TC_SINE_SELECTION,
  TC_SAT_SOLVER,
  TC_MINIMIZING_SOLVER,
  TC_SAT_PROOF_MINIMIZATION,
  TC_TERM_SHARING,
  TC_SORT_SHARING,  
  TC_SPLITTING_MODEL_UPDATE,
  TC_CONGRUENCE_CLOSURE,
  TC_CCMODEL,
  TC_SIMPLIFYING_UNIT_LITERAL_INDEX_MAINTENANCE,
  TC_NON_UNIT_LITERAL_INDEX_MAINTENANCE,
  TC_FORWARD_SUBSUMPTION_INDEX_MAINTENANCE,
  TC_FORWARD_SUBSUMPTION_DEMODULATION_INDEX_MAINTENANCE,
  TC_BINARY_RESOLUTION_INDEX_MAINTENANCE,
  TC_BACKWARD_SUBSUMPTION_INDEX_MAINTENANCE,
  TC_BACKWARD_SUPERPOSITION_INDEX_MAINTENANCE,
  TC_FORWARD_SUPERPOSITION_INDEX_MAINTENANCE,
  TC_BACKWARD_DEMODULATION_INDEX_MAINTENANCE,
  TC_FORWARD_DEMODULATION_INDEX_MAINTENANCE,
  TC_SPLITTING_COMPONENT_INDEX_MAINTENANCE,
  TC_SPLITTING_COMPONENT_INDEX_USAGE,
  TC_LITERAL_REWRITE_RULE_INDEX_MAINTENANCE,
  TC_INDUCTION_TERM_INDEX_MAINTENANCE,
  TC_UNIT_INTEGER_COMPARISON_INDEX_MAINTENANCE,
  TC_LRS_LIMIT_MAINTENANCE,
  TC_CONDENSATION,
  TC_INTERPRETED_EVALUATION,
  TC_FORWARD_SUBSUMPTION,
  TC_FORWARD_SUBSUMPTION_RESOLUTION,
  TC_FORWARD_SUBSUMPTION_DEMODULATION,
  TC_BACKWARD_SUBSUMPTION,
  TC_BACKWARD_SUBSUMPTION_RESOLUTION,
  TC_BACKWARD_SUBSUMPTION_DEMODULATION,
  TC_FORWARD_DEMODULATION,
  TC_BACKWARD_DEMODULATION,
  TC_FORWARD_LITERAL_REWRITING,
  TC_RESOLUTION,
  TC_UR_RESOLUTION,
  TC_SUPERPOSITION,
  TC_LITERAL_ORDER_AFTERCHECK,
  TC_HYPER_SUPERPOSITION,
  TC_GLOBAL_SUBSUMPTION,
  TC_INST_GEN_SIMPLIFICATIONS,
  TC_INST_GEN_VARIANT_DETECTION,
  TC_INST_GEN_SAT_SOLVING,
  TC_INST_GEN_GEN_INST,
  TC_CONSEQUENCE_FINDING,
  TC_DISMATCHING,
  TC_FMB_DEF_INTRO,
  TC_FMB_SORT_INFERENCE,
  TC_FMB_FLATTENING,
  TC_FMB_SPLITTING,
  TC_FMB_SAT_SOLVING,
  TC_FMB_CONSTRAINT_CREATION,
  TC_HCVI_COMPUTE_HASH,
  TC_HCVI_INSERT,
  TC_HCVI_RETRIEVE,
  TC_MINISAT_ELIMINATE_VAR,
  TC_MINISAT_BWD_SUBSUMPTION_CHECK,
  TC_Z3_IN_FMB,
  TC_NAMING,
  TC_LITERAL_SELECTION,
  TC_PASSIVE_CONTAINER_MAINTENANCE,
  TC_THEORY_INST_SIMP,
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
