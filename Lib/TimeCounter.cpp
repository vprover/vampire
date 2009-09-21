/**
 * @file TimeCounter.cpp
 * Implements class TimeCounter.
 */

#include "../Debug/Assertion.hpp"
#include "../Debug/Tracer.hpp"

#include "../Lib/Environment.hpp"
#include "../Lib/Timer.hpp"

#include "../Shell/Options.hpp"

#include "TimeCounter.hpp"

namespace Lib {

using namespace std;
using namespace Shell;


bool TimeCounter::s_measuring = true;
bool TimeCounter::s_initialized = false;
int TimeCounter::s_measuredTimes[__TC_ELEMENT_COUNT];
int TimeCounter::s_measureInitTimes[__TC_ELEMENT_COUNT];
int TimeCounter::s_measuredCnt = 0;

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
  ASS_EQ(s_measureInitTimes[TC_OTHER],-1);

  if(_tcu==__TC_NONE) {
    //we did not start measuring
    return;
  }
  ASS_GE(s_measureInitTimes[_tcu], 0);

  int currTime=env.timer->elapsedMilliseconds();
  s_measuredTimes[_tcu] += currTime-s_measureInitTimes[_tcu];

  s_measureInitTimes[_tcu]=-1;

  s_measuredCnt--;
  if(!s_measuredCnt) {
    s_measureInitTimes[TC_OTHER]=currTime;
  }
}

void TimeCounter::printReport()
{
  env.out<<"Time measurement results:"<<endl;
  for(int i=0; i<__TC_ELEMENT_COUNT; i++) {
    printSingleStat(static_cast<TimeCounterUnit>(i));
  }
  env.out<<endl;
}

void TimeCounter::printSingleStat(TimeCounterUnit tcu)
{
  if(s_measureInitTimes[tcu]==-1 && !s_measuredTimes[tcu]) {
    return;
  }
  switch(tcu) {
  case TC_BACKWARD_DEMODULATION:
    env.out<<"backward demodulation";
    break;
  case TC_BACKWARD_SUBSUMPTION:
    env.out<<"backward subsumption";
    break;
  case TC_BDD:
    env.out<<"BDD operations";
    break;
  case TC_FORWARD_DEMODULATION:
    env.out<<"forward demodulation";
    break;
  case TC_FORWARD_SUBSUMPTION:
    env.out<<"forward subsumption";
    break;
  case TC_SIMPLIFYING_UNIT_LITERAL_INDEX_MAINTENANCE:
    env.out<<"simplifying unit clause index maintenance";
    break;
  case TC_FORWARD_SUBSUMPTION_INDEX_MAINTENANCE:
    env.out<<"forward subsumption index maintenance";
    break;
  case TC_BINARY_RESOLUTION_INDEX_MAINTENANCE:
    env.out<<"binary resolution index maintenance";
    break;
  case TC_BACKWARD_SUBSUMPTION_INDEX_MAINTENANCE:
    env.out<<"backward subsumption index maintenance";
    break;
  case TC_BACKWARD_SUPERPOSITION_INDEX_MAINTENANCE:
    env.out<<"backward superposition index maintenance";
    break;
  case TC_FORWARD_SUPERPOSITION_INDEX_MAINTENANCE:
    env.out<<"forward superposition index maintenance";
    break;
  case TC_BACKWARD_DEMODULATION_INDEX_MAINTENANCE:
    env.out<<"backward demodulation index maintenance";
    break;
  case TC_FORWARD_DEMODULATION_INDEX_MAINTENANCE:
    env.out<<"forward demodulation index maintenance";
    break;
  case TC_SPLITTING_COMPONENT_INDEX_MAINTENANCE:
    env.out<<"splitting component index maintenance";
    break;
  case TC_OTHER:
    env.out<<"other";
    break;
  case TC_PARSING:
    env.out<<"parsing";
    break;
  case TC_PREPROCESSING:
    env.out<<"preprocessing";
    break;
  case TC_RESOLUTION:
    env.out<<"resolution";
    break;
  case TC_SUPERPOSITION:
    env.out<<"superposition";
    break;
  default:
    ASSERTION_VIOLATION;
  }
  env.out<<": ";

  int time=s_measuredTimes[tcu];
  if(s_measureInitTimes[tcu]!=-1) {
    time += env.timer->elapsedMilliseconds()-s_measureInitTimes[tcu];
  }
  env.out<<Timer::msToSecondsString(time)<<endl;
}

};
