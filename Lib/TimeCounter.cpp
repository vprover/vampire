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
 * @file TimeCounter.cpp
 * Implements class TimeCounter.
 */

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Timer.hpp"

#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"

#include "TimeCounter.hpp"

using namespace std;
using namespace Shell;
using namespace Lib;

bool TimeCounter::s_measuring = true;
bool TimeCounter::s_initialized = false;
int TimeCounter::s_measuredTimes[__TC_ELEMENT_COUNT];
int TimeCounter::s_measuredTimesChildren[__TC_ELEMENT_COUNT];
int TimeCounter::s_measureInitTimes[__TC_ELEMENT_COUNT];
TimeCounter* TimeCounter::s_currTop = 0;

/**
 * Reinitializes the time counting
 *
 * This is useful when we fork a new the process and want
 * to start counting from the beginning.
 */
void TimeCounter::reinitialize()
{
  CALL("TimeCounter::reinitialize");

  s_measuring = true;
  s_initialized=0;

  initialize();

  int currTime=env.timer->elapsedMilliseconds();

  TimeCounter* counter = s_currTop;
  while(counter) {
    s_measureInitTimes[counter->_tcu]=currTime;
    counter = counter->previousTop;
  }
  // at least OTHER is running, started now
  s_measureInitTimes[TC_OTHER] = currTime;
}

void TimeCounter::initialize()
{
  CALL("TimeCounter::initialize");
  ASS(!s_initialized);

  s_initialized=true;

  if(!env.options->timeStatistics()) {
    s_measuring=false;
    return;
  }

  for(int i=0; i<__TC_ELEMENT_COUNT; i++) {
    s_measuredTimes[i]=0;
    s_measuredTimesChildren[i]=0;
    s_measureInitTimes[i]=-1;
  }

  // OTHER is running, from time 0
  s_measureInitTimes[TC_OTHER]=0;
}

void TimeCounter::startMeasuring(TimeCounterUnit tcu)
{
  CALL("TimeCounter::startMeasuring");
  ASS_NEQ(tcu, TC_OTHER);

  TimeoutProtector tp; // let's not get interrupted while updating our TimeCounter linked-list

  if(!s_initialized) {
    initialize();
    if(!s_measuring) {
      return;
    }
  }

  // don't run a timer inside itself
  ASS_REP(s_measureInitTimes[tcu] == -1,tcu);

  previousTop = s_currTop;
  s_currTop = this;

  int currTime=env.timer->elapsedMilliseconds();

  _tcu=tcu;
  s_measureInitTimes[_tcu]=currTime;
}

void TimeCounter::stopMeasuring()
{
  CALL("TimeCounter::stopMeasuring");
  
  TimeoutProtector tp; // let's not get interrupted while updating our TimeCounter linked-list

  if(_tcu==__TC_NONE) {
    //we did not start measuring
    return;
  }
  ASS_GE(s_measureInitTimes[_tcu], 0);

  int currTime=env.timer->elapsedMilliseconds();
  int measuredTime = currTime-s_measureInitTimes[_tcu];
  s_measuredTimes[_tcu] += measuredTime;
  s_measureInitTimes[_tcu]=-1;

  if (previousTop) {
    s_measuredTimesChildren[previousTop->_tcu] += measuredTime;
  } else {
    s_measuredTimesChildren[TC_OTHER] += measuredTime;
  }

  ASS_EQ(s_currTop,this);
  s_currTop = previousTop;
}

void TimeCounter::snapShot()
{
  CALL("TimeCounter::snapShot");

  int currTime=env.timer->elapsedMilliseconds();

  TimeCounter* counter = s_currTop;
  while(counter) {
    ASS_GE(s_measureInitTimes[counter->_tcu], 0);
    int measuredTime = currTime-s_measureInitTimes[counter->_tcu];
    s_measuredTimes[counter->_tcu] += measuredTime;
    s_measureInitTimes[counter->_tcu]=currTime;

    if (counter->previousTop) {
      s_measuredTimesChildren[counter->previousTop->_tcu] += measuredTime;
    } else {
      s_measuredTimesChildren[TC_OTHER] += measuredTime;
    }

    counter = counter->previousTop;
  }

  int measuredTime = currTime-s_measureInitTimes[TC_OTHER];
  s_measuredTimes[TC_OTHER] += measuredTime;
  s_measureInitTimes[TC_OTHER]=currTime;
}

void TimeCounter::printReport(ostream& out)
{
  CALL("TimeCounter::printReport");

  snapShot();

  addCommentSignForSZS(out);
  out << "Time measurement results:" << endl;
  for (int i=0; i<__TC_ELEMENT_COUNT; i++) {
    outputSingleStat(static_cast<TimeCounterUnit>(i), out);
  }
  out<<endl;
}

void TimeCounter::outputSingleStat(TimeCounterUnit tcu, ostream& out)
{
  if (s_measureInitTimes[tcu]==-1 && !s_measuredTimes[tcu]) {
    return;
  }

  addCommentSignForSZS(out);
  switch(tcu) {
  case TC_RAND_OPT:
    out << "random option generation";
    break;
  case TC_BACKWARD_DEMODULATION:
    out<<"backward demodulation";
    break;
  case TC_BACKWARD_SUBSUMPTION:
    out<<"backward subsumption";
    break;
  case TC_BACKWARD_SUBSUMPTION_RESOLUTION:
    out<<"backward subsumption resolution";
    break;
  case TC_BACKWARD_SUBSUMPTION_DEMODULATION:
    out<<"backward subsumption demodulation";
    break;
  case TC_INTERPRETED_EVALUATION:
    out<<"interpreted evaluation";
    break;
  case TC_CONDENSATION:
    out<<"condensation";
    break;
  case TC_CONSEQUENCE_FINDING:
    out<<"consequence finding";
    break;
  case TC_FORWARD_DEMODULATION:
    out<<"forward demodulation";
    break;
  case TC_FORWARD_SUBSUMPTION:
    out<<"forward subsumption";
    break;
  case TC_FORWARD_SUBSUMPTION_RESOLUTION:
    out<<"forward subsumption resolution";
    break;
  case TC_FORWARD_SUBSUMPTION_DEMODULATION:
    out<<"forward subsumption demodulation";
    break;
  case TC_FORWARD_LITERAL_REWRITING:
    out<<"forward literal rewriting";
    break;
  case TC_GLOBAL_SUBSUMPTION:
    out<<"global subsumption";
    break;
  case TC_SIMPLIFYING_UNIT_LITERAL_INDEX_MAINTENANCE:
    out<<"unit clause index maintenance";
    break;
  case TC_NON_UNIT_LITERAL_INDEX_MAINTENANCE:
    out<<"non unit clause index maintenance";
    break;
  case TC_FORWARD_SUBSUMPTION_INDEX_MAINTENANCE:
    out<<"forward subsumption index maintenance";
    break;
  case TC_FORWARD_SUBSUMPTION_DEMODULATION_INDEX_MAINTENANCE:
    out<<"forward subsumption demodulation index maintenance";
    break;
  case TC_BINARY_RESOLUTION_INDEX_MAINTENANCE:
    out<<"binary resolution index maintenance";
    break;
  case TC_BACKWARD_SUBSUMPTION_INDEX_MAINTENANCE:
    out<<"backward subsumption index maintenance";
    break;
  case TC_BACKWARD_SUPERPOSITION_INDEX_MAINTENANCE:
    out<<"backward superposition index maintenance";
    break;
  case TC_FORWARD_SUPERPOSITION_INDEX_MAINTENANCE:
    out<<"forward superposition index maintenance";
    break;
  case TC_BACKWARD_DEMODULATION_INDEX_MAINTENANCE:
    out<<"backward demodulation index maintenance";
    break;
  case TC_FORWARD_DEMODULATION_INDEX_MAINTENANCE:
    out<<"forward demodulation index maintenance";
    break;
  case TC_SPLITTING_COMPONENT_INDEX_MAINTENANCE:
    out<<"splitting component index maintenance";
    break;
  case TC_SPLITTING_COMPONENT_INDEX_USAGE:
    out<<"splitting component index usage";
    break;
  case TC_SPLITTING_MODEL_UPDATE:
    out<<"splitting model update";
    break;
  case TC_CONGRUENCE_CLOSURE:
    out<<"congruence closure";
    break;
  case TC_CCMODEL:
    out<<"model from congruence closure";
    break;
  case TC_INST_GEN_SAT_SOLVING:
    out<<"inst gen SAT solving";
    break;
  case TC_INST_GEN_SIMPLIFICATIONS:
    out<<"inst gen simplifications";
    break;
  case TC_INST_GEN_VARIANT_DETECTION:
    out<<"inst gen variant detection";
    break;
  case TC_INST_GEN_GEN_INST:
    out<<"inst gen generating instances";
    break;
  case TC_LRS_LIMIT_MAINTENANCE:
    out<<"LRS limit maintenance";
    break;
  case TC_LITERAL_REWRITE_RULE_INDEX_MAINTENANCE:
    out<<"literal rewrite rule index maintenance";
    break;
  case TC_INDUCTION_TERM_INDEX_MAINTENANCE:
    out<<"induction term index maintenance";
    break;
  case TC_UNIT_INTEGER_COMPARISON_INDEX_MAINTENANCE:
    out<<"unit integer comparison literal index maintenance";
    break;
  case TC_OTHER:
    out<<"other";
    break;
  case TC_PARSING:
    out<<"parsing";
    break;
  case TC_PREPROCESSING:
    out<<"preprocessing";
    break;
  case TC_BCE:
    out<<"blocked clause elimination";
    break;
  case TC_PROPERTY_EVALUATION:
    out<<"property evaluation";
    break;
  case TC_SINE_SELECTION:
    out<<"sine selection";
    break;
  case TC_RESOLUTION:
    out<<"resolution";
    break;
  case TC_UR_RESOLUTION:
    out<<"unit resulting resolution";
    break;
  case TC_SAT_SOLVER:
    out<<"SAT solver time";
    break;
  case TC_MINIMIZING_SOLVER:
    out << "minimizing solver time";
    break;
  case TC_SAT_PROOF_MINIMIZATION:
    out << "sat proof minimization";
    break;
  case TC_SUPERPOSITION:
    out<<"superposition";
    break;
  case TC_LITERAL_ORDER_AFTERCHECK:
    out<<"literal order aftercheck";
    break;
  case TC_HYPER_SUPERPOSITION:
    out<<"hyper superposition";
    break;
  case TC_TERM_SHARING:
    out<<"term sharing";
    break;
  case TC_SORT_SHARING:
    out<<"sort sharing";
    break;    
  case TC_DISMATCHING:
    out << "dismatching";
    break;
  case TC_FMB_DEF_INTRO:
    out << "fmb definition introduction";
    break;
  case TC_FMB_SORT_INFERENCE:
    out << "fmb sort inference"; 
    break;
  case TC_FMB_FLATTENING:
    out << "fmb flattening";
    break;
  case TC_FMB_SPLITTING:
    out << "fmb splitting";
    break;
  case TC_FMB_SAT_SOLVING:
    out << "fmb sat solving";
    break;
  case TC_FMB_CONSTRAINT_CREATION:
    out << "fmb constraint creation";
    break;
  case TC_HCVI_COMPUTE_HASH:
    out << "hvci compute hash";
    break;
  case TC_HCVI_INSERT:
    out << "hvci insert";
    break;
  case TC_HCVI_RETRIEVE:
      out << "hvci retrieve";
      break;
  case TC_MINISAT_ELIMINATE_VAR:
    out << "minisat eliminate var";
    break;
  case TC_MINISAT_BWD_SUBSUMPTION_CHECK:
      out << "minisat bwd subsumption check";
      break;
  case TC_Z3_IN_FMB:
    out << "smt search for next domain size assignment";
    break;
  case TC_NAMING:
    out << "naming";
    break;
  case TC_LITERAL_SELECTION:
    out << "literal selection";
    break;
  case TC_PASSIVE_CONTAINER_MAINTENANCE:
    out << "passive container maintenance";
    break;
  case TC_THEORY_INST_SIMP:
    out << "theory instantiation and simplification";
    break;
  default:
    ASSERTION_VIOLATION;
  }
  out<<": ";

  Timer::printMSString(out, s_measuredTimes[tcu]);

  if (s_measuredTimesChildren[tcu] > 0) {
    out << " ( own ";
    Timer::printMSString(out, s_measuredTimes[tcu]-s_measuredTimesChildren[tcu]);
    out << " ) ";
  }
  
  out<<endl;
}

