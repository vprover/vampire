/**
 * @file SMTCOMPMode.cpp
 * Implements class SMTCOMPMode.
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "ForkingSM.hpp"

#include "SMTCOMPMode.hpp"

#define SLOWNESS 1.05

using namespace Lib;
using namespace SMTCOMP;

bool SMTCOMPMode::perform(int argc, char* argv [])
{
  CALL("SMTCOMPMode::perform/2");

  UIHelper::szsOutput=true;

  env.timer->makeChildrenIncluded();

#if COMPILER_MSVC
  USER_ERROR("Cannot run under Windows");
#else
  ForkingSM cm;
#endif

  bool res=cm.perform();

  return res;
}

void SMTCOMPMode::handleSIGINT()
{
  CALL("SMTCOMPMode::handleSIGINT");

  exit(VAMP_RESULT_STATUS_SIGINT);
}

bool SMTCOMPMode::perform()
{
  CALL("SMTCOMPMode::perform/0");

  Schedule quick;
  Schedule fallback;

  // no seperate sat/unsat schedules
  getSchedules(*_property, quick, fallback);
  
  int remainingTime=env.remainingTime()/100;
  if (remainingTime<=0) {
    return false;
  }
  StrategySet used;
  if (runSchedule(quick,remainingTime,used,false)) {
    return true;
  }
  remainingTime=env.remainingTime()/100;
  if (remainingTime<=0) {
    return false;
  }
  return runSchedule(fallback,remainingTime,used,true);
}

/**
 * Get schedules for a problem of given property.
 * The schedules are to be executed from the toop of the stack,
 */
void SMTCOMPMode::getSchedules(Property& property, Schedule& quick, Schedule& fallback)
{
  Property::Category cat = property.category();
  unsigned long prop = property.props();
  unsigned atoms = property.atoms();


} // getSchedule

unsigned SMTCOMPMode::getSliceTime(vstring sliceCode,vstring& chopped)
{
  CALL("SMTCOMPMode::getSliceTime");

  unsigned pos=sliceCode.find_last_of('_');
  vstring sliceTimeStr=sliceCode.substr(pos+1);
  chopped.assign(sliceCode.substr(0,pos));
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr,sliceTime));
  ASS_G(sliceTime,0); //strategies with zero time don't make sense

  unsigned time = (unsigned)(sliceTime * SLOWNESS) + 1;
  if (time < 10) {
    time++;
  }
  return time;
}


/**
 * Run strategies from the null-terminated array @b strategies,
 * so that the sequence would not take longer tham @b ds deciseconds
 *
 * The remaining time is always split between the remaining strategies
 * in the ratio of their hard-coded time (the last number in the
 * slice string).
 *
 * Return true iff the proof or satisfiability was found.
 *
 * For each strategy code, this code stripped off the time information will
 * be saved in ss.
 * If fallback is true and the code was previously in ss, the strategy will
 * not be run
 */
bool SMTCOMPMode::runSchedule(Schedule& schedule,unsigned ds,StrategySet& ss,bool fallback)
{
  CALL("SMTCOMPMode::runSchedule");

  Schedule::BottomFirstIterator sit(schedule);
  while (sit.hasNext()) {
    vstring sliceCode = sit.next();
    vstring chopped;
    unsigned sliceTime = getSliceTime(sliceCode,chopped);
    if (fallback && ss.contains(chopped)) {
      continue;
    }
    ss.insert(chopped);
    int remainingTime = env.remainingTime()/100;
    if (remainingTime<=0) {
      return false;
    }
    // cast to unsigned is OK since realTimeRemaining is positive
    if (sliceTime > (unsigned)remainingTime) {
      sliceTime = remainingTime;
    }
    if (runSlice(sliceCode,sliceTime)) {
      return true;
    }
  }
  return false;
} // runSchedule

bool SMTCOMPMode::runSlice(vstring slice, unsigned ds)
{
  CALL("SMTCOMPMode::runSlice");


  // Copy options - it is import options can be copied nicely
  Options opt=*env.options;
  opt.readFromEncodedOptions(slice);
  opt.setTimeLimitInDeciseconds(ds);
  int stl = opt.simulatedTimeLimit();
  if (stl) {
    opt.setSimulatedTimeLimit(int(stl * SLOWNESS));
  }
  return runSlice(opt);
}

