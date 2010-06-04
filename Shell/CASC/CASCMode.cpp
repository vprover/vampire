/**
 * @file CASCMode.cpp
 * Implements class CASCMode.
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Timer.hpp"

#include "ForkingCM.hpp"
#include "SpawningCM.hpp"

#include "CASCMode.hpp"

namespace Shell
{
namespace CASC
{

using namespace Lib;

const char* ltbStrategies[] = {
    "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_600",
    "dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_600",
    "dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_600",
    "dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_600",
    "dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_600",
    "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_600",
    "lrs+4_6_bd=off:bs=off:cond=on:flr=on:fde=none:nwc=4:nicw=on:ptb=off:ssec=off:sio=off:spl=backtracking_600",
    "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_600",
    "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_600",
    "lrs-1010_4_bd=off:bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=axioms:st=2.0:sos=on:spo=on:spl=backtracking:sp=occurrence_600",
    "dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_600",
    "dis+1003_8_bms=on:ecs=on:lcm=predicate:nwc=3.0:ssec=off:sgo=on:sio=off:spo=on:sp=occurrence:updr=off_600",
    "dis+10_10_bs=off:gsp=input_only:lcm=reverse:nwc=10.0:nicw=on:sswn=on:sgo=on_600",
    0
};


bool CASCMode::perform(int argc, char* argv [])
{
  CALL("CASCMode::perform");

  env.timer->makeChildrenIncluded();

  if(!system(0)) {
    USER_ERROR("The CASC mode is not supported on this system (the \"int system(const char *)\" function is not available)");
  }

  SpawningCM cm(argv[0]);

  return cm.perform();
}

bool CASCMode::perform()
{
  CALL("CASCMode::perform");

  unsigned remainingTime=env.remainingTime()/100;

  return runStrategySet(ltbStrategies, remainingTime);
}

unsigned CASCMode::getStrategyTime(string st)
{
  CALL("CASCMode::getStrategyTime");

  string stTimeStr=st.substr(st.find_last_of('_')+1);
  unsigned stTime;
  ALWAYS(Int::stringToUnsignedInt(stTimeStr, stTime));
  ASS_G(stTime,0); //strategies with zero time don't make sense

  return stTime;
}

/**
 * Run strategies from the null-terminated array @b strategies,
 * so that the sequence would not take longer tham @b ds deciseconds
 *
 * Return true iff the proof or satisfiability was found
 */
bool CASCMode::runStrategySet(const char** strategies, unsigned ds)
{
  CALL("CASCMode::runStrategySet");

  unsigned startTime=env.timer->elapsedDeciseconds();
  unsigned finishTime=startTime+ds;

  static Stack<string> stStack;
  stStack.reset();

  unsigned strategyTimeSum=0;

  const char** ptr=strategies;
  while(*ptr) {
    string st(*ptr);
    stStack.push(st);
    strategyTimeSum+=getStrategyTime(st);
    ptr++;
  }

  unsigned strategyTimeRemaining=strategyTimeSum;

  Stack<string>::BottomFirstIterator stIt(stStack);
  while(stIt.hasNext()) {
    string st=stIt.next();
    unsigned stTime=getStrategyTime(st);

    int realTimeRemaining=finishTime-env.timer->elapsedDeciseconds();
    if(realTimeRemaining<=0) {
      return false;
    }
    unsigned rTime=(realTimeRemaining*stTime)/strategyTimeRemaining;
    strategyTimeRemaining-=stTime;

    env.out<<"% remaining time: "<<realTimeRemaining<<" next slice time: "<<rTime<<endl;

    if(runStrategy(st, rTime)) {
      return true;
    }
  }
  return false;
}


}
}
