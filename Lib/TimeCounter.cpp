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
}

void TimeCounter::startMeasuring(TimeCounterUnit tcu)
{
  CALL("TimeCounter::startMeasuring");

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

  _tcu=tcu;
  s_measureInitTimes[_tcu]=env.timer->elapsedMilliseconds();
}

void TimeCounter::stopMeasuring()
{
  CALL("TimeCounter::stopMeasuring");

  if(_tcu==__TC_NONE) {
    //we did not start measuring
    return;
  }
  ASS_GE(s_measureInitTimes[_tcu], 0);

  int finishTime=env.timer->elapsedMilliseconds();
  s_measuredTimes[_tcu] += finishTime-s_measureInitTimes[_tcu];

  s_measureInitTimes[_tcu]=-1;
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
  case TC_INDEX_MAINTENANCE:
    env.out<<"index maintenance";
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

  if(s_measureInitTimes[tcu]==-1) {
    env.out<<s_measuredTimes[tcu];
  } else {
    int time=s_measuredTimes[tcu];
    time += env.timer->elapsedMilliseconds()+s_measureInitTimes[tcu];
    env.out<<time<<" and running";
  }
  env.out<<endl;
}

};
