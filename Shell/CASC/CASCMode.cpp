/**
 * @file CASCMode.cpp
 * Implements class CASCMode.
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Timer.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "ForkingCM.hpp"
#include "SpawningCM.hpp"

#include "CASCMode.hpp"

namespace Shell
{
namespace CASC
{

using namespace Lib;

bool CASCMode::perform(int argc, char* argv [])
{
  CALL("CASCMode::perform/2");

  env.timer->makeChildrenIncluded();

#if COMPILER_MSVC
  SpawningCM cm(argv[0]);
#else
  ForkingCM cm;
#endif

  bool res=cm.perform();
  if(res) {
    env.out<<"% Success!"<<endl;
  }
  else {
    env.out<<"% Proof not found"<<endl;
  }
  env.statistics->print();
  return res;
}

void CASCMode::handleSIGINT()
{
  CALL("CASCMode::handleSIGINT");

  env.out<<"% Terminated by SIGINT!"<<endl;
  env.statistics->print();
  exit(3);
}

bool CASCMode::perform()
{
  CALL("CASCMode::perform/0");

  Property::Category cat = _property.category();
  const char** quickSlices;
  const char** slowSlices;
  const char* backupSlices[] = {0};
  switch (cat) {
  case Property::NEQ: {
    break;
  }
  case Property::HEQ: {
    break;
  }
  case Property::PEQ: {
    break;
  }
  case Property::HNE: {
    break;
  }
  case Property::NNE: {
    break;
  }
  case Property::FEQ: {
    break;
  }
  case Property::FNE: {
    break;
  }
  case Property::EPR: {
    break;
  }
  case Property::UEQ: {
    break;
  }
  }
    const char* quick[] = {
      "lrs+1010_4_cond=on:flr=on:nwc=1.2:nicw=on:sswn=on:stl=94.6:sac=on:sio=off:spo=on_46",
      "lrs-4_28_bd=off:flr=on:ptb=off:ssec=off:stl=63.1:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_2",
      "dis-10_28_ep=on:fsr=off:fde=none:nwc=1.5:ptb=off:ssec=off:sos=on:sgo=on:sp=reverse_arity:updr=off_78",
      "lrs+1003_5_flr=on:fde=none:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=63.1:sos=on:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:updr=off_139",
      "dis+1003_8_bs=off:flr=on:fsr=off:gsp=input_only:nwc=1.2:ssec=off:sac=on:sgo=on:sio=off:sp=occurrence_119",
      "lrs-1010_8_bs=off:cond=fast:ep=on:fsr=off:gsp=input_only:nwc=1.1:nicw=on:sswn=on:sswsr=on:stl=63.1:sac=on:updr=off_86",
      "lrs-1_5_bs=off:bms=on:cond=fast:fsr=off:gsp=input_only:nwc=1.2:nicw=on:sswn=on:stl=63.1:sac=on:sp=reverse_arity_179",
      "lrs+1010_8_cond=on:flr=on:nwc=1:sswn=on:sswsr=on:stl=63.1:sac=on:sgo=on:spo=on:updr=off_224",
      "dis+10_10_bs=off:ep=on:nwc=1.1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_327",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "lrs+1010_4_cond=on:flr=on:nwc=1.2:nicw=on:sswn=on:stl=94.6:sac=on:sio=off:spo=on_507",
      "lrs-4_28_bd=off:flr=on:ptb=off:ssec=off:stl=63.1:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_601",
      "dis-10_28_ep=on:fsr=off:fde=none:nwc=1.5:ptb=off:ssec=off:sos=on:sgo=on:sp=reverse_arity:updr=off_373",
      "dis+10_2_bd=off:cond=on:ecs=on:flr=on:gsp=input_only:nwc=5.0:nicw=on:ssec=off:sio=off:spl=off:sp=occurrence:updr=off_328",
      "dis+1003_8_bs=off:flr=on:fsr=off:gsp=input_only:nwc=1.2:ssec=off:sac=on:sgo=on:sio=off:sp=occurrence_532",
      0
    };
    slowSlices = slow;
  unsigned remainingTime=env.remainingTime()/100;
  if (runSchedule(quickSlices,remainingTime)) {
    return true;
  }
  remainingTime=env.remainingTime()/100;
  if(remainingTime<=0) {
    return false;
  }
  if (runSchedule(slowSlices,remainingTime)) {
    return true;
  }
  if(remainingTime<=0) {
    return false;
  }
  return runSchedule(backupSlices,remainingTime);
}

unsigned CASCMode::getSliceTime(string sliceCode)
{
  CALL("CASCMode::getSliceTime");

  string sliceTimeStr=sliceCode.substr(sliceCode.find_last_of('_')+1);
  unsigned sliceTime;
  ALWAYS(Int::stringToUnsignedInt(sliceTimeStr, sliceTime));
  ASS_G(sliceTime,0); //strategies with zero time don't make sense

  return sliceTime;
}

/**
 * Run strategies from the null-terminated array @b strategies,
 * so that the sequence would not take longer tham @b ds deciseconds
 *
 * The remaining time is always split between the remaining strategies
 * in the ratio of their hard-coded time (the last number in the
 * slice string).
 *
 * Return true iff the proof or satisfiability was found
 */
 bool CASCMode::runSchedule(const char** schedule, unsigned ds)
{
  CALL("CASCMode::runSchedule");

  for (const char** ptr=schedule; *ptr; ptr++) {
    string sliceCode(*ptr);
    unsigned sliceTime = getSliceTime(sliceCode);
    int remainingTime = env.remainingTime()/100;
    if(remainingTime<=0) {
      return false;
    }

    // cast to unsigned is OK since realTimeRemaining is positive
    if(sliceTime > (unsigned)remainingTime) {
      sliceTime = remainingTime;
    }
    env.out<<"% remaining time: "<<remainingTime<<" next slice time: "<<sliceTime<<endl;
    if(runSlice(sliceCode,sliceTime)) {
      return true;
    }
  }
  return false;
}

bool CASCMode::runSlice(string slice, unsigned ds)
{
  CALL("CASCMode::runSlice");

  Options opt=*env.options;
  opt.readFromTestId(slice);
  opt.setTimeLimitInDeciseconds(ds);
  return runSlice(opt);
}

}
}
