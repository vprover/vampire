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

#include "TimeCounter.hpp"

namespace Lib {

using namespace std;
using namespace Shell;


bool TimeCounter::s_measuring = true;
bool TimeCounter::s_initialized = false;
int TimeCounter::s_measuredTimes[__TC_ELEMENT_COUNT];
int TimeCounter::s_measureInitTimes[__TC_ELEMENT_COUNT];
int TimeCounter::s_measuredCnt = 0;


/**
 * Reinitializes the time counting
 *
 * This is useful when we fork a new the process and want
 * to start counting from begining.
 */
void TimeCounter::reinitialize()
{
  CALL("TimeCounter::reinitialize");

  Stack<int> measured;
  for(int i=0; i<__TC_ELEMENT_COUNT; i++) {
    if(isBeingMeasured(static_cast<TimeCounterUnit>(i))) {
      measured.push(i);
    }
  }

  s_initialized=0;

  initialize();

  int currTime=env.timer->elapsedMilliseconds();

  while(measured.isNonEmpty()) {
    int i=measured.pop();
    s_measureInitTimes[i]=currTime;
  }
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
    s_measureInitTimes[i]=-1;
  }

  s_measureInitTimes[TC_OTHER]=0;
}

void TimeCounter::startMeasuring(TimeCounterUnit tcu)
{
  CALL("TimeCounter::startMeasuring");
  ASS_NEQ(tcu, TC_OTHER);

  if(!s_initialized) {
    initialize();
    if(!s_measuring) {
      return;
    }
  }

  if(s_measureInitTimes[tcu]!=-1) {
    //the tcu unit is already being measured
    _tcu=__TC_NONE;
    return;
  }

  int currTime=env.timer->elapsedMilliseconds();

  _tcu=tcu;
  s_measureInitTimes[_tcu]=currTime;

  if(!s_measuredCnt) {
    ASS_NEQ(s_measureInitTimes[TC_OTHER],-1);
    s_measuredTimes[TC_OTHER]+=currTime-s_measureInitTimes[TC_OTHER];
    s_measureInitTimes[TC_OTHER]=-1;
  }

  s_measuredCnt++;
}

void TimeCounter::stopMeasuring()
{
  CALL("TimeCounter::stopMeasuring");

  if(_tcu==__TC_NONE) {
    //we did not start measuring
    return;
  }
  ASS_EQ(s_measureInitTimes[TC_OTHER],-1);
  ASS_GE(s_measureInitTimes[_tcu], 0);

  int currTime=env.timer->elapsedMilliseconds();
  s_measuredTimes[_tcu] += currTime-s_measureInitTimes[_tcu];

  s_measureInitTimes[_tcu]=-1;

  s_measuredCnt--;
  if(!s_measuredCnt) {
    s_measureInitTimes[TC_OTHER]=currTime;
  }
}

void TimeCounter::printReport(ostream& out)
{
  out<<"Time measurement results:"<<endl;
  for(int i=0; i<__TC_ELEMENT_COUNT; i++) {
    outputSingleStat(static_cast<TimeCounterUnit>(i), out);
  }
  out<<endl;
}

void TimeCounter::outputSingleStat(TimeCounterUnit tcu, ostream& out)
{
  if(s_measureInitTimes[tcu]==-1 && !s_measuredTimes[tcu]) {
    return;
  }
  switch(tcu) {
  case TC_BACKWARD_DEMODULATION:
    out<<"backward demodulation";
    break;
  case TC_BACKWARD_SUBSUMPTION:
    out<<"backward subsumption";
    break;
  case TC_BACKWARD_SUBSUMPTION_RESOLUTION:
    out<<"backward subsumption resolution";
    break;
  case TC_BDD:
    out<<"BDD operations";
    break;
  case TC_BDD_CLAUSIFICATION:
    out<<"BDD clausification";
    break;
  case TC_BDD_MARKING_SUBSUMPTION:
    out<<"BDD marking subsumption";
    break;
  case TC_INTERPRETED_EVALUATION:
    out<<"interpreted evaluation";
    break;
  case TC_INTERPRETED_SIMPLIFICATION:
    out<<"interpreted simplification";
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
  case TC_INST_GEN_SAT_SOLVING:
    out<<"inst gen SAT solving";
    break;
  case TC_INST_GEN_SIMPLIFICATIONS:
    out<<"inst gen simplifications";
    break;
  case TC_LRS_LIMIT_MAINTENANCE:
    out<<"LRS limit maintenance";
    break;
  case TC_LITERAL_REWRITE_RULE_INDEX_MAINTENANCE:
    out<<"literal rewrite rule index maintenance";
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
    out<<"SAT solver";
    break;
  case TC_SUPERPOSITION:
    out<<"superposition";
    break;
  case TC_TERM_SHARING:
    out<<"term sharing";
    break;
  default:
    ASSERTION_VIOLATION;
  }
  out<<": ";

  int time=s_measuredTimes[tcu];
  if(s_measureInitTimes[tcu]!=-1) {
    time += env.timer->elapsedMilliseconds()-s_measureInitTimes[tcu];
  }
  
  Timer::printMSString(out, time);
  out<<endl;
}

};
