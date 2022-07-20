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
  case TC_OTHER:
    out<<"other";
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

