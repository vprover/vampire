/**
 * @file CASCMode.cpp
 * Implements class CASCMode.
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


#include "Kernel/MainLoop.hpp"
#include "Kernel/MainLoopScheduler.hpp"

#include "ForkingCM.hpp"
#include "SpawningCM.hpp"
#include "MultiCM.hpp"

#include "CASCMode.hpp"

#define SLOWNESS 1.1

using namespace Lib;
using namespace CASC;

bool CASCMode::_sat = false;
bool CASCMode::_epr = false;
bool CASCMode::_multi_strategy = false;

bool CASCMode::perform(int argc, char* argv [])
{
  CALL("CASCMode::perform/2");

  UIHelper::cascMode=true;

  bool res=false;
  if(_multi_strategy){
    MultiCM cm;
    res=cm.perform();
  }
  else{
    env -> timer->makeChildrenIncluded();
#if COMPILER_MSVC
    SpawningCM cm(argv[0]);
#else
    ForkingCM cm;
#endif
    res=cm.perform();
  }


  env -> beginOutput();
  if (res) {
    env -> out()<<"% Success in time "<<Timer::msToSecondsString(env -> timer->elapsedMilliseconds())<<endl;
  }
  else {
    env -> out()<<"% Proof not found in time "<<Timer::msToSecondsString(env -> timer->elapsedMilliseconds())<<endl;
    if (env -> remainingTime()/100>0) {
      env -> out()<<"% SZS status GaveUp for "<<env -> options->problemName()<<endl;

    }
    else {
      //From time to time we may also be terminating in the timeLimitReached()
      //function in Lib/Timer.cpp in case the time runs out. We, however, output
      //the same string there as well.
      env -> out()<<"% SZS status Timeout for "<<env -> options->problemName()<<endl;
    }
  }
  if (env -> options && env -> options->timeStatistics()) {
    TimeCounter::printReport(env -> out());
  }
  env -> endOutput();

  return res;
}

void CASCMode::handleSIGINT()
{
  CALL("CASCMode::handleSIGINT");

  env -> beginOutput();
  env -> out()<<"% Terminated by SIGINT!"<<endl;
  env -> out()<<"% SZS status User for "<<env -> options->problemName() <<endl;
  env -> statistics->print(env -> out());
  env -> endOutput();
  exit(VAMP_RESULT_STATUS_SIGINT);
}

bool CASCMode::perform()
{
  CALL("CASCMode::perform/0");

  cout << "Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!\n";

  Schedule quick;
  Schedule fallback;

  if (_sat) {
    getSchedulesSat(*_property, quick, fallback);
  }
  else if (_epr) {
    getSchedulesEPR(*_property, quick, fallback);
  }
  else {
    getSchedules(*_property, quick, fallback);
  }

  int remainingTime=env -> remainingTime()/100;
  if (remainingTime<=0) {
    return false;
  }
  if(_multi_strategy){
    //TODO this belongs in MultiCM
    transformToOptionsList(quick);
    
    Problem* prb = UIHelper::getInputProblem(*env -> options);
    Kernel::MainLoopScheduler scheduler(*prb, *env -> optionsList);
    scheduler.run();

    int resultValue=1;
    //return value to zero if we were successful
#if SATISFIABLE_IS_SUCCESS
    if(env -> statistics->terminationReason==Statistics::REFUTATION ||
       env -> statistics->terminationReason==Statistics::SATISFIABLE) {
#else
    if(env -> statistics->terminationReason==Statistics::REFUTATION) {
#endif
      resultValue=0;
    }

    env -> beginOutput();
    UIHelper::outputResult(env -> out());
    env -> endOutput();

    //To use fallback we would need to perform this on top of Forking
    return resultValue;
  }
  else{ 
    StrategySet used;
    if (runSchedule(quick,remainingTime,used,false)) {
      return true;
    }
    remainingTime=env -> remainingTime()/100;
    if (remainingTime<=0) {
      return false;
    }
    return runSchedule(fallback,remainingTime,used,true);
  }
}

void CASCMode::transformToOptionsList(Schedule& schedule)
{
  CALL("CASCMode::transformToOptionsList");
  ASS(env->optionsList);

}

/**
 * Get schedules for a problem of given property.
 * The schedules are to be executed from the toop of the stack,
 */
void CASCMode::getSchedules(Property& property, Schedule& quick, Schedule& fallback)
{
  Property::Category cat = property.category();
  unsigned prop = property.props();
  unsigned atoms = property.atoms();

  switch (cat) {
  case Property::NEQ:
    if (prop == 131079) {
      quick.push("dis+11_4:1_bs=off:cond=fast:drc=off:nwc=10:sio=off:spl=sat:sser=off:ssnc=none_8");
      quick.push("ott+3_8:1_bd=off:bs=off:bsr=unit_only:drc=off:fsr=off:nwc=2.5:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=1.0:ssnc=none:updr=off_12");
      quick.push("dis+11_2_bs=off:bsr=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:sio=off:spl=sat:sser=off:ssnc=none_23");
      quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_5");
      quick.push("dis+11_4_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=1.7:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_68");
      quick.push("ott+11_2_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:ep=on:fde=none:lcm=reverse:nwc=1.2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_36");
      quick.push("dis+1011_10_bs=off:drc=off:fsr=off:nwc=10:sos=on:sio=off:spl=sat:ssnc=none_29");
      quick.push("dis+1011_24_cond=fast:drc=off:nwc=10:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_120");
      quick.push("ott+10_4:1_bd=off:bs=off:bsr=unit_only:drc=off:nwc=2:nicw=on:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on:updr=off_117");
      quick.push("dis+11_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_18");
      quick.push("ott+1011_3_bs=off:bsr=unit_only:fde=none:nwc=2:sio=off:spl=sat:ssfq=1.0:ssnc=none_55");
      quick.push("ott+11_2_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sp=reverse_arity_228");
      quick.push("dis+11_64_bs=off:drc=off:fde=none:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence_283");
      quick.push("ott+11_8:1_drc=off:ep=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none:sp=occurrence:updr=off_480");
      quick.push("dis+1011_64_bs=off:drc=off:nwc=2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_44");
      quick.push("ott+11_8:1_bs=off:drc=off:flr=on:lcm=predicate:nwc=2:sos=all:sio=off:spo=on:sfv=off_110");
    }
    else if (prop == 1) {
      if (atoms > 175) {
	quick.push("ott+2_1_bs=off:cond=on:drc=off:ep=on:nwc=1.7:nicw=on:ss=axioms:sos=all:sio=off:urr=on_1");
	quick.push("dis+1011_10_bs=off:drc=off:fsr=off:nwc=10:sos=on:sio=off:spl=sat:ssnc=none_2");
	quick.push("dis-1010_3:1_bs=off:drc=off:ep=RS:flr=on:nwc=5:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_2");
	quick.push("dis+1011_6_bs=off:drc=off:ep=on:fde=none:nwc=1.1:sio=off:spl=sat:sser=off:ssnc=none_38");
	quick.push("dis+10_8:1_bs=off:br=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=1:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_29");
	quick.push("ott+11_2:3_bs=off:drc=off:flr=on:lcm=predicate:nwc=2.5:sio=off:spl=sat:sser=off:ssfp=100000:ssnc=none:sp=occurrence_57");
	quick.push("ott-11_2:3_bs=off:drc=off:fsr=off:lcm=predicate:nwc=5:nicw=on:sac=on:sio=off:spo=on:sp=reverse_arity_26");
	quick.push("dis-1002_2:3_bs=off:drc=off:gsp=input_only:nwc=1.7:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sp=occurrence_3");
	quick.push("dis+1011_64_bs=off:drc=off:nwc=2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_1");
	quick.push("dis-11_28_bs=off:drc=off:flr=on:lcm=predicate:nwc=1.7:sos=on:sio=off:spl=sat:ssfq=1.0:ssnc=none_48");
	quick.push("ott-11_40_bd=off:bs=off:drc=off:flr=on:fsr=off:lcm=predicate:nwc=10:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:updr=off_42");
	quick.push("ott+1_3:1_bs=off:br=off:drc=off:flr=on:lcm=predicate:nwc=1.7:sio=off:spl=sat:ssfp=10000:ssfq=1.4:ssnc=none:sp=occurrence:urr=on_11");
	quick.push("ott+11_50_bd=off:bs=off:drc=off:ep=on:lcm=reverse:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssnc=none:sfv=off_56");
	quick.push("dis+11_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_33");
	quick.push("dis+10_1024_bs=off:drc=off:flr=on:fsr=off:nwc=1.1:sio=off:spl=sat:ssfq=1.4:ssnc=none_76");
	quick.push("ott+1_1024_bs=off:br=off:cond=on:drc=off:flr=on:gs=on:nwc=2.5:nicw=on:sd=1:ss=axioms:st=1.2:sac=on:sio=off:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=all_dependent:urr=on:updr=off_65");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_72");
	quick.push("lrs+2_64_bd=off:bs=off:br=off:cond=on:drc=off:flr=on:fde=none:nwc=1.7:stl=30:sio=off:spl=sat:ssfp=1000:ssfq=1.4:ssnc=none:urr=on_54");
	quick.push("lrs+1011_14_bd=off:bs=off:cond=on:drc=off:ep=on:lcm=predicate:nwc=1.7:stl=60:sio=off:spo=on:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:urr=on_211");
	quick.push("ott+11_8:1_bs=off:drc=off:flr=on:lcm=predicate:nwc=2:sos=all:sio=off:spo=on:sfv=off_171");
	quick.push("dis+10_1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:sos=on:sio=off:spl=sat:sser=off:ssnc=none_1");
	quick.push("ott+11_8:1_drc=off:ep=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none:sp=occurrence:updr=off_16");
	quick.push("ott+11_2_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:ep=on:fde=none:lcm=reverse:nwc=1.2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_101");
      }
      else {
	quick.push("dis+3_4_bs=off:br=off:cond=on:drc=off:ep=RSTC:nwc=4:nicw=on:sos=all:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:urr=on_2");
	quick.push("dis+11_64_bs=off:drc=off:fde=none:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence_15");
	quick.push("ins+1_3:1_bs=off:cond=on:ep=RSTC:flr=on:gs=on:igbrr=0.8:igrr=1/4:igrp=400:igrpq=1.1:igwr=on:nwc=1.5:sio=off:urr=on_4");
	quick.push("dis+1011_1024_bs=unit_only:drc=off:gsp=input_only:nwc=1.1:sio=off:spo=on:urr=on_10");
	quick.push("ott+11_2_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sp=reverse_arity_4");
	quick.push("dis+11_3:1_bs=off:cond=fast:drc=off:nwc=5:sio=off:spl=sat:sser=off:ssnc=none_17");
	quick.push("ott+10_28_bd=off:bs=off:drc=off:nwc=1.5:sio=off:spl=sat:ssnc=none_21");
	quick.push("lrs+2_14_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:nwc=1.1:stl=30:sio=off:spl=sat:ssac=none:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence:updr=off_227");
	quick.push("lrs+4_24_bd=off:bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:stl=60:sio=off:spl=sat:ssfp=4000:ssfq=1.2:ssnc=none_540");
	quick.push("ott+10_64_bd=off:bs=off:drc=off:flr=on:gsp=input_only:lcm=predicate:nwc=2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_212");
	quick.push("ott+11_3_bd=off:bs=off:drc=off:ep=on:flr=on:nwc=1:sio=off:spl=sat:ssfq=1.1:ssnc=none:sfv=off_46");
      }
    }
    else if (prop == 3) {
      if (atoms <= 2000) {
	quick.push("dis+11_8:1_bs=off:cond=fast:drc=off:ep=on:nwc=10:nicw=on:sio=off:spl=sat:ssnc=none:urr=on_8");
	quick.push("ott+10_4:1_bd=off:bs=off:bsr=unit_only:drc=off:nwc=2:nicw=on:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on:updr=off_95");
	quick.push("ott+2_1_bs=off:cond=on:drc=off:ep=on:nwc=1.7:nicw=on:ss=axioms:sos=all:sio=off:urr=on_23");
	quick.push("ott+1_1024_bs=off:br=off:cond=on:drc=off:flr=on:gs=on:nwc=2.5:nicw=on:sd=1:ss=axioms:st=1.2:sac=on:sio=off:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=all_dependent:urr=on:updr=off_2");
	quick.push("ott+1011_3_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.2:sio=off:spl=sat:ssfq=1.4:ssnc=none_69");
	quick.push("dis+4_8:1_bs=off:drc=off:ep=RS:nwc=2:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=sat:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_20");
	quick.push("ins+2_5_bs=off:cond=fast:ep=RSTC:flr=on:gs=on:igbrr=0.7:igrr=1/4:igrp=700:igrpq=1.2:igwr=on:lcm=reverse:nwc=2:sio=off:urr=on_5");
	quick.push("dis+2_24_bs=off:cond=fast:drc=off:fsr=off:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=2.0:ssnc=none_1");
	quick.push("ott+11_3_bd=off:bs=off:drc=off:ep=on:flr=on:nwc=1:sio=off:spl=sat:ssfq=1.1:ssnc=none:sfv=off_46");
	quick.push("dis+1002_4:1_bs=off:cond=fast:drc=off:ep=RST:nwc=3:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_25");
	quick.push("ott+10_2_bd=off:bs=off:drc=off:flr=on:fsr=off:nwc=1.7:sio=off:spl=sat:ssfq=2.0:ssnc=none_91");
	quick.push("lrs+10_1_bs=off:cond=fast:nwc=5:stl=20:sio=off:spl=sat:ssfq=1.1:ssnc=none_4");
	quick.push("dis+1011_64_bs=off:drc=off:ep=on:flr=on:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_50");
	quick.push("dis+1011_1024_bs=unit_only:cond=fast:lcm=reverse:nwc=1.1:sos=on:sio=off:spl=sat:sser=off:ssnc=none:sfv=off_48");
	quick.push("dis+1_8:1_bs=off:drc=off:lcm=reverse:nwc=1.5:sos=all:sio=off:spl=sat:ssfq=2.0:ssnc=none:sfv=off_96");
	quick.push("dis+1011_2_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on:updr=off_202");
	quick.push("lrs+2_3_bd=off:cond=on:drc=off:flr=on:nwc=1.3:stl=30:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off:sp=reverse_arity_96");
	quick.push("ott+11_2:3_bs=off:drc=off:flr=on:lcm=predicate:nwc=2.5:sio=off:spl=sat:sser=off:ssfp=100000:ssnc=none:sp=occurrence_256");
	quick.push("dis+10_8:1_bs=off:br=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=1:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_140");
	quick.push("dis+2_4:1_bs=unit_only:cond=on:flr=on:lcm=predicate:nwc=1:ssac=none:ssfp=100000:ssfq=2.0:ssnc=all:sfv=off:urr=on_257");
	quick.push("dis+1011_6_bs=off:drc=off:ep=on:fde=none:nwc=1.1:sio=off:spl=sat:sser=off:ssnc=none_106");
      }
      else {
	quick.push("dis-1010_3:1_bs=off:drc=off:ep=RS:flr=on:nwc=5:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_3");
	quick.push("ott+1011_3_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.2:sio=off:spl=sat:ssfq=1.4:ssnc=none_27");
	quick.push("dis+10_10_bs=off:cond=fast:drc=off:gs=on:nwc=1.7:nicw=on:sd=1:ss=axioms:st=3.0_2");
	quick.push("dis-1002_5:1_bs=off:cond=fast:drc=off:ep=on:nwc=1.1:sd=4:ss=axioms:sos=on:sio=off:spl=sat:urr=on_17");
	quick.push("ott-11_2:3_bs=off:drc=off:fsr=off:lcm=predicate:nwc=5:nicw=on:sac=on:sio=off:spo=on:sp=reverse_arity_14");
	quick.push("dis+11_4:1_bs=off:drc=off:gsp=input_only:nwc=3:sos=on_23");
	quick.push("dis+4_8:1_bs=off:drc=off:ep=RS:nwc=2:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=sat:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_2");
	quick.push("dis+2_24_bs=off:cond=fast:drc=off:fsr=off:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=2.0:ssnc=none_2");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_31");
	quick.push("ott+2_1_bs=off:cond=on:drc=off:ep=on:nwc=1.7:nicw=on:ss=axioms:sos=all:sio=off:urr=on_2");
	quick.push("dis+3_8:1_bs=off:drc=off:fsr=off:fde=none:nwc=10:sio=off:spl=sat:ssfp=10000:ssfq=1.4:ssnc=none:sp=reverse_arity_17");
	quick.push("ins-1010_8:1_bs=off:ep=RSTC:fsr=off:igbrr=1.0:igrr=1/128:igrp=700:igrpq=1.5:igwr=on:nwc=3:sos=on:sgo=on:sio=off_70");
	quick.push("ott-1010_2:1_bs=off:cond=fast:drc=off:nwc=3:sd=1:ss=axioms:st=2.0:sio=off:spl=sat:sser=off:ssnc=none_36");
	quick.push("dis+1_8:1_bs=off:drc=off:lcm=reverse:nwc=1.5:sos=all:sio=off:spl=sat:ssfq=2.0:ssnc=none:sfv=off_90");
	quick.push("ott+1_10_bd=off:bs=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_111");
	quick.push("ott+1_1024_bs=off:br=off:cond=on:drc=off:flr=on:gs=on:nwc=2.5:nicw=on:sd=1:ss=axioms:st=1.2:sac=on:sio=off:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=all_dependent:urr=on:updr=off_246");
	quick.push("lrs+2_3:1_bs=off:br=off:cond=fast:drc=off:flr=on:nwc=4:stl=60:sio=off:spo=on:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_250");
	quick.push("lrs+1011_14_bd=off:bs=off:cond=on:drc=off:ep=on:lcm=predicate:nwc=1.7:stl=60:sio=off:spo=on:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:urr=on_549");
      }
    }
    else {
      quick.push("dis+11_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_8");
      quick.push("dis+1011_1024_bs=unit_only:cond=fast:lcm=reverse:nwc=1.1:sos=on:sio=off:spl=sat:sser=off:ssnc=none:sfv=off_6");
      quick.push("dis+11_8:1_bs=off:drc=off:ep=RS:nwc=10:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_2");
      quick.push("dis+2_2:3_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=1:nicw=on:sos=all:sio=off:spl=sat:ssfq=1.1:ssnc=none:urr=on_7");
      quick.push("ott+1011_3_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.2:sio=off:spl=sat:ssfq=1.4:ssnc=none_12");
      quick.push("dis+2_5_cond=fast:drc=off:fsr=off:lcm=reverse:nwc=3:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none_9");
      quick.push("dis-1010_6_bs=off:drc=off:ep=on:gsp=input_only:nwc=10:nicw=on:sos=all:sp=occurrence_13");
      quick.push("dis+11_4:1_bs=off:drc=off:gsp=input_only:nwc=3:sos=on_1");
      quick.push("dis+2_24_bs=off:cond=fast:drc=off:fsr=off:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=2.0:ssnc=none_4");
      quick.push("dis+11_24_bs=off:cond=fast:drc=off:nwc=2.5:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:urr=on_1");
      quick.push("dis+10_1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:sos=on:sio=off:spl=sat:sser=off:ssnc=none_19");
      quick.push("lrs-1010_3_bs=unit_only:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=1.1:nicw=on:stl=30:sos=on:sac=on:sio=off_3");
      quick.push("dis+11_20_bs=off:cond=fast:fde=none:lcm=reverse:nwc=3:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=reverse_arity_9");
      quick.push("lrs-1002_6_bs=off:bsr=unit_only:cond=fast:fde=none:gsp=input_only:lcm=reverse:nwc=1:stl=30:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=occurrence_11");
      quick.push("dis-1002_3:2_bs=off:cond=fast:drc=off:ep=RST:flr=on:fde=none:lcm=predicate:nwc=10:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:updr=off_8");
      quick.push("lrs+1010_24_bd=off:bs=off:cond=on:drc=off:gsp=input_only:nwc=1.3:nicw=on:stl=10:sio=off:spo=on:spl=sat:sser=off:ssfq=1.0:ssnc=none:updr=off_18");
      quick.push("dis+1002_4:1_bs=off:cond=fast:drc=off:ep=RST:nwc=3:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_10");
      quick.push("dis-1002_12_bs=off:cond=on:drc=off:ep=on:gsp=input_only:nwc=10:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_1");
      quick.push("dis+11_64_bs=off:drc=off:fde=none:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence_26");
      quick.push("dis+1011_6_bs=off:drc=off:ep=on:fde=none:nwc=1.1:sio=off:spl=sat:sser=off:ssnc=none_30");
      quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_252");
      quick.push("dis+11_4_ep=on:fde=none:lcm=reverse:nwc=10:sos=on:sio=off:spl=sat:ssnc=none_240");
      quick.push("ins+2_5_bs=off:cond=fast:ep=RSTC:flr=on:gs=on:igbrr=0.7:igrr=1/4:igrp=700:igrpq=1.2:igwr=on:lcm=reverse:nwc=2:sio=off:urr=on_1");
      quick.push("dis+1011_64_bs=off:drc=off:nwc=2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_26");
      quick.push("dis-1002_2:3_bs=off:drc=off:gsp=input_only:nwc=1.7:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sp=occurrence_60");
    }
    break;

  case Property::HEQ:
    if (prop == 2) {
      quick.push("dis+11_10_bs=off:drc=off:nwc=10:sos=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_3");
      quick.push("ott+11_128_bs=off:drc=off:gsp=input_only:gs=on:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence_626");
      quick.push("dis+11_5:4_bs=off:cond=fast:drc=off:fde=none:nwc=1:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.2:ssnc=none:urr=on_164");
      quick.push("ins+2_64_bs=off:cond=on:drc=off:flr=on:fde=none:igbrr=0.1:igrr=1/16:igrpq=1.3:igwr=on:nwc=1.7:sp=reverse_arity_1061");
    }
    else if (prop == 8194) {
      quick.push("lrs+11_2:1_bs=off:cond=on:drc=off:nwc=10:stl=60:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_487");
      quick.push("lrs+11_3:1_bs=unit_only:drc=off:fde=none:nwc=10:stl=60:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none_128");
      quick.push("lrs+2_4_bs=off:cond=fast:drc=off:gsp=input_only:nwc=4:stl=90:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none_335");
      quick.push("ott+11_3:2_bs=off:cond=on:drc=off:ep=RSTC:flr=on:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfp=10000:ssnc=none_205");
    }
    else {
      quick.push("ott+11_24_bd=off:bs=off:drc=off:nwc=3:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_2");
      quick.push("ins+11_64_bs=off:cond=on:drc=off:fde=none:igbrr=0.2:igrr=1/64:igrp=400:igrpq=1.05:igwr=on:nwc=1.2:sio=off_29");
      quick.push("dis+2_8_bd=off:bs=off:ep=RST:fsr=off:lcm=reverse:nwc=10:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off_2");
      quick.push("dis-1002_3_bs=off:cond=fast:drc=off:nwc=10:nicw=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_2");
      quick.push("dis+10_1024_bd=off:bs=off:cond=on:drc=off:fde=none:nwc=2.5:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:urr=on_162");
      quick.push("lrs-1_2_bs=off:drc=off:nwc=4:nicw=on:stl=30:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none_236");
      quick.push("ins+4_5:4_bs=off:br=off:cond=on:ep=RSTC:flr=on:fsr=off:igbrr=0.1:igrr=1/16:igrpq=1.0:igwr=on:nwc=2:urr=on_323");
      quick.push("ott+11_24_bs=unit_only:cond=fast:drc=off:nwc=3:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_473");
    }
    break;
    
  case Property::PEQ:
    if (prop == 0) {
      if (atoms <= 15) {
	quick.push("dis+10_1024_bs=unit_only:cond=on:drc=off:nwc=1:sio=off:spl=sat:ssfq=1.0:ssnc=none_35");
	quick.push("lrs+3_4_bsr=unit_only:drc=off:fsr=off:nwc=1:stl=150:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:urr=on_490");
	quick.push("lrs+4_14_cond=on:drc=off:flr=on:nwc=3:stl=180:spl=sat:sser=off:ssnc=none_947");
      }
      else {
	quick.push("dis-1010_14_bs=off:drc=off:gsp=input_only:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none_12");
	quick.push("dis+10_64_bd=off:cond=fast:drc=off:nwc=3:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.1:ssnc=none_241");
	quick.push("ott+11_5_bs=off:cond=fast:drc=off:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=1.2:ssnc=none_753");
	quick.push("ott+11_2:3_bd=off:drc=off:nwc=4:nicw=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:updr=off_243");
	quick.push("dis+2_7_bd=off:drc=off:flr=on:fsr=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off_441");
      }
    }
    else if (prop == 1) {
      quick.push("lrs-1_128_bs=off:cond=fast:ep=on:nwc=1.2:nicw=on:stl=30:sac=on:sio=off_14");
      quick.push("dis-1003_128_drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_40");
      quick.push("lrs+3_40_bs=unit_only:bsr=on:cond=on:drc=off:fsr=off:nwc=1.1:nicw=on:stl=100:sio=off:spl=sat:ssfq=1.2:ssnc=none:urr=on:updr=off_645");
      quick.push("dis+10_64_bd=off:cond=fast:drc=off:nwc=3:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.1:ssnc=none_115");
      quick.push("dis+1_2_bd=off:bs=off:drc=off:flr=on:fsr=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_278");
      quick.push("dis+2_7_bd=off:drc=off:flr=on:fsr=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off_544");
      quick.push("lrs+3_4_bsr=unit_only:drc=off:fsr=off:nwc=1:stl=150:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:urr=on_1006");
    }
    else {
      quick.push("dis-1010_14_bs=off:drc=off:gsp=input_only:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none_18");
      quick.push("ott+3_4:1_bsr=unit_only:cond=on:drc=off:fsr=off:fde=none:gs=on:nwc=1:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence:urr=on_13");
      quick.push("lrs+3_16_bsr=unit_only:cond=on:drc=off:fsr=off:nwc=4:stl=150:sio=off:spl=sat:ssnc=none:urr=on_141");
      quick.push("lrs+10_2:3_bd=off:cond=on:drc=off:flr=on:nwc=5:nicw=on:stl=90:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_85");
      quick.push("dis-1004_1024_bs=off:cond=fast:drc=off:nwc=1.3:sio=off:spl=sat:ssfq=1.4:ssnc=none_72");
      quick.push("ott+11_3_bd=off:bs=unit_only:bsr=unit_only:drc=off:fsr=off:nwc=1.5:sio=off:spo=on:spl=sat:ssfp=10000:ssfq=1.2:ssnc=none_39");
      quick.push("ott+2_20_bs=off:cond=fast:drc=off:fde=none:nwc=2:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:sp=occurrence_116");
      quick.push("ott-1003_8_bs=off:bsr=on:cond=on:drc=off:fsr=off:gs=on:nwc=5:sac=on:sio=off:sp=occurrence_156");
      quick.push("ins+1_20_bsr=on:br=off:cond=fast:drc=off:fsr=off:fde=none:igbrr=0.3:igrr=1/32:igrp=4000:igrpq=2.0:igwr=on:lcm=reverse:nwc=1.2:sgo=on:sio=off:sp=occurrence:urr=on_159");
      quick.push("ott+3_128_bs=off:drc=off:nwc=1.1:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence_321");
    }
    break;

  case Property::HNE:
    if (prop == 8192) {
      if (atoms > 6) {
	quick.push("ott+4_6_bs=off:bsr=unit_only:cond=fast:nwc=3:nicw=on:sio=off:spl=sat:ssnc=none_76");
	quick.push("dis-1004_5:1_bs=off:cond=on:nwc=2:sio=off_17");
	quick.push("dis+11_2:3_bs=off:cond=fast:fsr=off:nwc=10:sio=off:spl=sat:sser=off:ssnc=none_125");
	quick.push("ott+1011_10_bs=off:cond=on:nwc=3:sio=off:spl=sat:ssnc=none_61");
	quick.push("lrs+10_3:2_bs=off:cond=fast:nwc=10:stl=90:sio=off:spo=on_127");
	quick.push("ott+1003_28_bs=off:cond=on:flr=on:fsr=off:lcm=predicate:nwc=1:nicw=on:sio=off:spl=off_275");
	quick.push("dis+2_5:4_cond=fast:flr=on:lcm=predicate:nwc=1.5:sio=off:spl=off_562");
	quick.push("dis+1002_64_bs=off:fsr=off:gsp=input_only:lcm=predicate:nwc=1.2:nicw=on:sio=off:spo=on_391");
	quick.push("lrs+10_8:1_bs=off:cond=fast:flr=on:fsr=off:nwc=2.5:stl=90:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_601");
      }
      else {
	quick.push("dis+1011_20_bs=off:fsr=off:nwc=2:sio=off:spl=off_103");
	quick.push("lrs+3_4_bs=off:cond=fast:flr=on:nwc=1:nicw=on:stl=30:sio=off:spl=sat:ssnc=none_172");
	quick.push("lrs+11_128_cond=fast:lcm=reverse:nwc=1.5:nicw=on:stl=60:sio=off:spl=sat:ssfp=100000:ssfq=2.0:ssnc=none_525");
	quick.push("lrs+1011_64_bs=unit_only:bsr=unit_only:cond=fast:flr=on:nwc=1:stl=180:sio=off:spl=sat:ssfq=2.0_611");
      }
    }
    else {
      quick.push("dis+1011_14_bs=off:nwc=4:sio=off:spl=off_2");
      quick.push("dis+10_3_bs=off:br=off:cond=fast:gs=on:nwc=1:sos=all:sio=off:urr=on_22");
      quick.push("ott+1011_10_bs=off:cond=on:nwc=3:sio=off:spl=sat:ssnc=none_14");
      quick.push("ott+4_6_bs=off:bsr=unit_only:cond=fast:nwc=3:nicw=on:sio=off:spl=sat:ssnc=none_1");
      quick.push("ott+1011_20_bs=off:cond=fast:nwc=5:sio=off:spl=off_7");
      quick.push("lrs+10_3:1_bs=off:cond=on:flr=on:nwc=10:stl=50:sio=off:spl=off:sp=reverse_arity_62");
      quick.push("ott+1_8:1_bs=off:cond=on:gs=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssnc=none_178");
      quick.push("lrs+10_3:2_bs=off:cond=fast:nwc=10:stl=90:sio=off:spo=on_16");
      quick.push("ott+1011_10_bs=off:cond=fast:flr=on:fsr=off:nwc=1.7:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_21");
    }
    break;

  case Property::NNE:
    quick.push("dis+1011_50_bs=off:cond=fast:flr=on:gsp=input_only:nwc=1.3:sos=all_102");
    quick.push("dis-1010_14_bsr=on:cond=on:nwc=1.5:sio=off:spl=sat:ssfp=100000:ssfq=1.1:ssnc=none_69");
    quick.push("dis+11_20_bs=off:fsr=off:gsp=input_only:lcm=reverse:nwc=1.3:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_13");
    quick.push("dis-2_16_bs=off:cond=fast:flr=on:lcm=predicate:nwc=1:nicw=on:sagn=off:sio=off:spl=sat:ssnc=none_50");
    quick.push("ott+1011_5_bs=off:gs=on:nwc=2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssnc=none_33");
    quick.push("dis+1011_16_bs=unit_only:cond=on:fsr=off:gsp=input_only:nwc=1.7:sos=all:sgo=on:sio=off:spl=sat:ssfq=2.0:ssnc=all_60");
    quick.push("ott-1002_1024_cond=on:flr=on:gs=on:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.1:ssnc=none:urr=on_42");
    quick.push("dis+1011_12_bs=off:cond=fast:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_778");
    quick.push("dis+4_12_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_216");
    quick.push("dis+1011_40_bs=off:gsp=input_only:nwc=4:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_146");
    quick.push("dis+11_128_bs=off:cond=fast:flr=on:lcm=reverse:nwc=2:sio=off:spl=sat:ssnc=none_176");
    quick.push("dis+1011_128_bs=off:cond=fast:flr=on:fsr=off:lcm=reverse:nwc=2.5:nicw=on:sio=off:spl=sat:ssnc=none_217");
    break;

  case Property::FEQ:
    if (prop == 131075) {
      if (atoms > 3000) {
	quick.push("dis-1002_3_bs=off:cond=on:drc=off:ep=RS:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none_19");
	quick.push("ins+1011_6_bs=off:bsr=unit_only:cond=on:ep=RSTC:fde=none:igbrr=0.2:igrr=8/1:igrp=1400:igrpq=1.5:igwr=on:nwc=1.1:sos=on_15");
	quick.push("dis-1002_8_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:nwc=1.7:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off:updr=off_15");
	quick.push("ott+1011_5:4_bs=off:cond=fast:drc=off:flr=on:fsr=off:nwc=2:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_63");
	quick.push("ott+10_8:1_bd=off:bs=off:cond=fast:drc=off:flr=on:nwc=1.3:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:urr=on_15");
	quick.push("dis-1010_3:2_bs=off:drc=off:ep=on:nwc=3:sac=on:sgo=on:sio=off:spo=on:sfv=off_41");
	quick.push("dis+10_8:1_bs=off:br=off:cond=on:drc=off:ep=RST:fsr=off:nwc=1.3:sd=4:ss=axioms:st=3.0:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_89");
	quick.push("ins-1003_7_bs=off:ep=RSTC:flr=on:igbrr=0.0:igrr=1/128:igrp=1400:igrpq=1.1:igwr=on:nwc=1.3:sos=on:sio=off:spl=off_223");
	quick.push("lrs+1011_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1:nicw=on:stl=240:sos=all:sio=off:spo=on:ssac=none:ssfp=1000:ssfq=1.1:ssnc=all_dependent_737");
	quick.push("ott+1011_2:3_bs=off:br=off:cond=on:drc=off:gs=on:nwc=10:sd=1:ss=axioms:st=1.2:spl=sat:sser=off:urr=on_11");
      }
      else {
	quick.push("dis-1002_8_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:nwc=1.7:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off:updr=off_1");
	quick.push("dis+11_28_bd=off:bs=off:cond=fast:drc=off:ep=on:fsr=off:lcm=reverse:nwc=5:sos=on:sio=off:spl=sat:ssfq=1.0:ssnc=none:sp=occurrence_10");
	quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_1");
	quick.push("ins-1010_3:2_bs=unit_only:drc=off:ep=on:fde=none:igbrr=0.5:igrr=1/128:igrpq=1.3:igwr=on:nwc=1.7_35");
	quick.push("ott+2_8:1_bs=off:bsr=on:drc=off:fde=none:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_75");
	quick.push("dis+10_8:1_bs=off:br=off:cond=on:drc=off:ep=RST:fsr=off:nwc=1.3:sd=4:ss=axioms:st=3.0:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_21");
	quick.push("lrs+11_4_cond=fast:drc=off:flr=on:lcm=reverse:nwc=10:stl=50:sos=on:sio=off:spl=sat:ssfp=100000:ssfq=1.4:ssnc=none:sp=reverse_arity_4");
	quick.push("ott+1011_8:1_bs=off:drc=off:fde=none:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off:sp=occurrence_30");
	quick.push("lrs-1_5:1_bs=off:cond=fast:drc=off:nwc=4:stl=120:sio=off:spl=sat:ssfp=4000:ssfq=2.0:ssnc=none_8");
	quick.push("dis+1010_12_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:ssnc=none:sfv=off_179");
	quick.push("dis+1011_10_bd=off:bs=off:drc=off:ep=RS:fsr=off:nwc=1:nicw=on_8");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none_182");
	quick.push("lrs+1_6_bs=off:drc=off:nwc=3:stl=360:sos=all:sio=off:spl=sat:ssac=none:sscc=on:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_167");
	quick.push("ins+10_2:3_bs=unit_only:flr=on:fde=none:igbrr=0.7:igrr=1/32:igrp=200:igrpq=1.0:igwr=on:lcm=predicate:nwc=1.7:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=off_92");
	quick.push("lrs-1004_32_bs=off:br=off:cond=fast:drc=off:flr=on:gs=on:lcm=reverse:nwc=1:nicw=on:stl=30:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:urr=on_132");
	quick.push("dis-1_3_bsr=unit_only:drc=off:lcm=reverse:nwc=4:sos=all:sac=on:sgo=on:sio=off:spo=on:sp=reverse_arity_144");
	quick.push("lrs-1010_7_bs=unit_only:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1.7:stl=30:sgo=on:spo=on:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_291");
	quick.push("ott+1011_5:4_bs=off:cond=fast:drc=off:flr=on:fsr=off:nwc=2:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_298");
      }
    }
    else if (prop == 1) {
      if (atoms > 125) {
	quick.push("dis-10_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=4:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence_8");
	quick.push("ott+11_50_bs=off:cond=on:drc=off:fde=none:lcm=reverse:nwc=3:sos=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=reverse_arity:urr=on_7");
	quick.push("ins+11_3:1_bd=off:bs=off:cond=fast:drc=off:igbrr=0.9:igrr=1/128:igrp=200:igrpq=1.2:igwr=on:lcm=predicate:nwc=1:sos=all:sp=occurrence_1");
	quick.push("ott-1003_24_drc=off:nwc=2:sio=off:spl=sat:ssfp=1000:ssfq=2.0:ssnc=none:urr=on_2");
	quick.push("ott+1010_5_bd=off:bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_1");
	quick.push("dis-1002_3_bs=off:cond=on:drc=off:ep=RS:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none_190");
	quick.push("ott+11_10_bs=off:bsr=unit_only:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_10");
	quick.push("dis+1011_14_bd=off:bs=off:cond=fast:drc=off:nwc=4:sio=off:spl=sat:ssfq=1.0:ssnc=none_54");
	quick.push("dis+1_2:3_bs=off:drc=off:lcm=predicate:nwc=3:nicw=on:ss=included:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off:sp=occurrence_168");
	quick.push("ott+1_3:1_bd=off:bs=off:bsr=unit_only:ep=on:nwc=10:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=sat_80");
	quick.push("dis+11_32_bs=off:nwc=1.1:sio=off:spl=off:updr=off_198");
	quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_12");
      }
      else {
	quick.push("dis+1010_12_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:ssnc=none:sfv=off_13");
	quick.push("ott-1002_5:1_bs=off:bsr=on:cond=fast:drc=off:gsp=input_only:nwc=2:sos=all:sio=off:spo=on:urr=on_3");
	quick.push("dis+1011_2_bs=off:drc=off:nwc=1.1:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:sfv=off:urr=on_3");
	quick.push("dis+1011_10_bs=off:drc=off:nwc=1.3:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off_3");
	quick.push("dis+1011_1_bs=off:drc=off:nwc=1.2:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=2.0:ssnc=none_6");
	quick.push("dis-1002_3_bs=off:cond=on:drc=off:ep=RS:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none_1");
	quick.push("dis+2_2:3_bs=off:drc=off:lcm=reverse:nwc=2.5:sos=all:sser=off:ssfp=10000:ssfq=2.0:ssnc=all_8");
	quick.push("ott+10_1024_bs=off:cond=on:drc=off:gsp=input_only:nwc=1.2:sio=off:spl=sat:ssfp=10000:ssnc=none:updr=off_23");
	quick.push("ott-1010_3_bd=off:bs=off:bsr=unit_only:drc=off:fde=none:nwc=1:nicw=on:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_114");
	quick.push("ott+11_1_bs=off:drc=off:ep=RS:flr=on:fde=none:nwc=4:sos=all:sgo=on:sio=off_121");
	quick.push("ott+1_2:3_bs=off:cond=fast:drc=off:flr=on:lcm=predicate:nwc=1.3:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_197");
	quick.push("ott+4_64_bd=off:bs=off:br=off:cond=on:drc=off:fsr=off:gs=on:nwc=1.7:sos=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:urr=on_795");
      }
    }
    else if (prop == 0) {
      if (atoms < 8) {
      quick.push("ott+10_4_bs=off:drc=off:nwc=3:nicw=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:sp=occurrence_1");
      quick.push("ott-1010_64_bs=off:br=off:drc=off:flr=on:gs=on:nwc=1:sac=on:sio=off:urr=on_424");
      quick.push("lrs+1011_8_bd=off:bs=unit_only:bsr=on:drc=off:lcm=reverse:nwc=1:nicw=on:stl=270:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_1841");
      }
      else if (atoms < 12) {
	quick.push("lrs+10_20_bs=off:drc=off:nwc=1.1:nicw=on:stl=90:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_774");
      }
      else if (atoms < 15) {
	quick.push("lrs-1004_12_bs=off:bsr=unit_only:drc=off:nwc=1.7:nicw=on:stl=60:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.4:ssnc=none_473");
	quick.push("lrs+1_6_bs=off:drc=off:nwc=3:stl=360:sos=all:sio=off:spl=sat:ssac=none:sscc=on:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_1806");
      }
      else if (atoms < 50) {
	quick.push("dis+4_5_bs=off:drc=off:lcm=reverse:nwc=1.1:sos=all:sio=off:spl=sat:ssfp=40000:ssfq=1.4:ssnc=none:sp=occurrence_2");
	quick.push("ott+3_7_bs=off:cond=fast:nwc=3:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sio=off:spl=sat_4");
	quick.push("dis+1010_12_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:ssnc=none:sfv=off_33");
	quick.push("lrs-1_10_bs=off:cond=fast:drc=off:nwc=1.5:nicw=on:stl=20:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.4:ssnc=none_127");
	quick.push("ins+4_2_bd=off:bs=off:gs=on:igbrr=0.8:igrr=1/32:igrp=2000:igrpq=1.2:igwr=on:lcm=reverse:nwc=10:urr=on_3");
	quick.push("ott+11_10_bs=off:bsr=unit_only:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_126");
	quick.push("ott-3_10_bs=off:br=off:drc=off:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:urr=on_66");
	quick.push("ins-11_3:1_bs=off:cond=on:drc=off:fsr=off:igbrr=0.5:igrp=100:igrpq=1.0:igwr=on:lcm=predicate:nwc=1.1:sos=all:sio=off:spl=off:sp=reverse_arity_12");
	quick.push("dis+4_2:1_bs=off:br=off:drc=off:fsr=off:nwc=1:sos=all:sio=off:spl=sat:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_148");
	quick.push("lrs-11_6_bs=off:bsr=unit_only:drc=off:gsp=input_only:lcm=predicate:nwc=10:stl=30:sos=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on:updr=off_132");
	quick.push("lrs+10_20_bs=off:drc=off:nwc=1.1:nicw=on:stl=90:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_354");
	quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_220");
	quick.push("lrs-1_5:1_bs=off:cond=fast:drc=off:nwc=4:stl=120:sio=off:spl=sat:ssfp=4000:ssfq=2.0:ssnc=none_569");
	quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_1");
	quick.push("ott-1003_24_drc=off:nwc=2:sio=off:spl=sat:ssfp=1000:ssfq=2.0:ssnc=none:urr=on_46");
      }
      else if (atoms < 150) {
	quick.push("ott+10_3:1_bsr=unit_only:cond=fast:fsr=off:lcm=reverse:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:urr=on:updr=off_23");
	quick.push("ott+4_32_bs=off:flr=on:nwc=4:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_272");
	quick.push("lrs-2_6_bs=off:cond=fast:drc=off:nwc=4:nicw=on:stl=30:spo=on:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_4");
	quick.push("ott+10_24_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:sser=off:ssnc=none_288");
	quick.push("dis+2_20_drc=off:ep=RST:nwc=1.3:sio=off:spl=sat:ssfq=1.4:ssnc=none:sp=occurrence_62");
	quick.push("dis+4_40_cond=on:drc=off:flr=on:lcm=predicate:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_149");
	quick.push("ott+10_8:1_bd=off:bs=off:cond=fast:drc=off:flr=on:nwc=1.3:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:urr=on_77");
	quick.push("lrs+10_20_bs=off:drc=off:nwc=1.1:nicw=on:stl=90:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_551");
      }
      else if (atoms < 900) {
	quick.push("ins-1010_3:2_bs=unit_only:drc=off:ep=on:fde=none:igbrr=0.5:igrr=1/128:igrpq=1.3:igwr=on:nwc=1.7_30");
	quick.push("dis+1011_3_bs=off:cond=fast:drc=off:fsr=off:fde=none:gs=on:nwc=1.1:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_71");
	quick.push("dis-1010_4:1_bs=off:drc=off:lcm=predicate:nwc=2:nicw=on:sio=off_165");
	quick.push("ott-1010_64_bs=off:br=off:drc=off:flr=on:gs=on:nwc=1:sac=on:sio=off:urr=on_498");
	quick.push("ott+11_10_bs=off:bsr=unit_only:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_929");
      }
      else {
	quick.push("dis+1011_1_bs=off:drc=off:nwc=1.2:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=2.0:ssnc=none_20");
	quick.push("ins-1010_3:2_bs=unit_only:drc=off:ep=on:fde=none:igbrr=0.5:igrr=1/128:igrpq=1.3:igwr=on:nwc=1.7_55");
	quick.push("ott+11_1024_bd=off:bs=off:br=off:cond=fast:drc=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfq=1.2:ssnc=none:urr=on_127");
	quick.push("dis+4_10_bs=off:drc=off:flr=on:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=10000:ssfq=1.4:ssnc=none_274");
	quick.push("ott-1010_64_bs=off:br=off:drc=off:flr=on:gs=on:nwc=1:sac=on:sio=off:urr=on_560");
	quick.push("dis-1010_3:1_bd=off:bs=off:cond=fast:gs=on:lcm=reverse:nwc=1.1:sac=on_505");
      }
    }
    else if (prop == 131087) {
      if (atoms > 140000) {
	quick.push("dis-1002_6_bs=off:cond=on:drc=off:fde=none:nwc=1.5:sd=1:ss=included:sos=on:sagn=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_23");
	quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_98");
	quick.push("dis+10_8:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.1:nicw=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spl=sat:sp=reverse_arity_39");
	quick.push("ott+1_2_bs=off:drc=off:ep=on:nwc=3:nicw=on:sd=2:sgt=20:ss=axioms:sos=on:sagn=off:spl=sat:sser=off_43");
	quick.push("ott+2_3:1_bs=off:br=off:drc=off:nwc=1.1:nicw=on:sd=3:ss=axioms:st=3.0:sos=all:sio=off:spl=off:urr=on_22");
	quick.push("dis-1010_2:3_bs=off:drc=off:nwc=3:sd=2:ss=axioms:st=1.5:sac=on:sio=off_20");
	quick.push("dis+1_3_bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sd=1:ss=included:st=2.0:sagn=off:sio=off:spl=sat:sser=off:ssnc=none_134");
	quick.push("dis+1011_10_bs=off:drc=off:nwc=1.3:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off_95");
	quick.push("dis+11_3:1_bs=off:br=off:cond=on:drc=off:ep=on:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spl=sat:sser=off:urr=on_24");
	quick.push("dis-4_4:1_bs=off:ep=RST:gsp=input_only:gs=on:nwc=5:sd=1:ss=included:st=5.0:sos=on:sio=off:sfv=off:sp=occurrence_16");
	quick.push("ott+1_2:3_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=1.3:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_136");
	quick.push("ott+4_40_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=5:nicw=on:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:spl=sat:sser=off:updr=off_33");
	quick.push("ott+1011_8:1_bs=off:drc=off:fde=none:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off:sp=occurrence_51");
	quick.push("ott+1_3:1_bd=off:bs=off:bsr=unit_only:ep=on:nwc=10:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=sat_42");
	quick.push("dis-1002_16_bs=off:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off_47");
	quick.push("dis-2_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=1.5:sd=3:sgt=10:ss=axioms:sos=on:spl=sat_168");
	quick.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=2.5:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_129");
	quick.push("ott+10_8:1_bd=off:bs=off:drc=off:fde=none:gsp=input_only:nwc=1:sd=3:ss=axioms:sos=on:sio=off:spl=off:urr=on_213");
	quick.push("ott+10_2:3_bs=off:drc=off:gs=on:nwc=1.5:sd=2:ss=axioms:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:urr=on_111");
	quick.push("ott+11_2:1_bs=off:br=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:sd=2:ss=axioms:st=1.5:sos=all:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:urr=on_121");
	quick.push("dis-10_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=4:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence_149");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=10:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_305");
      }
      else if (atoms > 70000) {
	quick.push("ott+1011_8:1_bs=off:drc=off:fde=none:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off:sp=occurrence_13");
	quick.push("ott+11_2:1_bs=off:br=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:sd=2:ss=axioms:st=1.5:sos=all:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:urr=on_16");
	quick.push("ott+1_2_bs=off:drc=off:ep=on:nwc=3:nicw=on:sd=2:sgt=20:ss=axioms:sos=on:sagn=off:spl=sat:sser=off_17");
	quick.push("dis+2_1_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=1:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off_19");
	quick.push("dis-1002_6_bs=off:cond=on:drc=off:fde=none:nwc=1.5:sd=1:ss=included:sos=on:sagn=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_9");
	quick.push("dis-1002_40_bs=off:ep=RST:flr=on:gs=on:lcm=predicate:nwc=2.5:nicw=on:sd=5:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:ssnc=none:sp=reverse_arity_8");
	quick.push("dis+10_8:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.1:nicw=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spl=sat:sp=reverse_arity_40");
	quick.push("dis-1010_2_bd=off:bs=off:cond=fast:drc=off:nwc=5:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off:sp=occurrence_37");
	quick.push("ott+1_2:3_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=1.3:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_64");
	quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_86");
	quick.push("dis+11_3:1_bs=off:br=off:cond=on:drc=off:ep=on:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spl=sat:sser=off:urr=on_9");
	quick.push("dis-2_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=1.5:sd=3:sgt=10:ss=axioms:sos=on:spl=sat_87");
	quick.push("dis-1002_16_bs=off:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off_19");
	quick.push("dis-10_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=4:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence_63");
	quick.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=2.5:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_103");
	quick.push("dis+1_3_bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sd=1:ss=included:st=2.0:sagn=off:sio=off:spl=sat:sser=off:ssnc=none_135");
	quick.push("ott+1011_3:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.5:sd=3:ss=axioms:sos=all:sio=off:spl=off_276");
	quick.push("dis-1010_1024_bs=off:cond=fast:drc=off:fde=none:nwc=1:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_76");
	quick.push("dis+2_8:1_bd=off:bs=off:bsr=on:drc=off:lcm=reverse:nwc=4:nicw=on:sd=3:sgt=5:ss=axioms:st=1.5:sos=on:spl=sat:sser=off:sp=reverse_arity_104");
	quick.push("ott+10_8:1_bd=off:bs=off:drc=off:fde=none:gsp=input_only:nwc=1:sd=3:ss=axioms:sos=on:sio=off:spl=off:urr=on_122");
	quick.push("ott+10_2:3_bs=off:drc=off:gs=on:nwc=1.5:sd=2:ss=axioms:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:urr=on_275");
	quick.push("dis+1011_10_bs=off:drc=off:nwc=1.3:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off_142");
	quick.push("dis-1002_8_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:nwc=1.7:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off:updr=off_11");
      }
      else if (atoms > 3200) {
	quick.push("dis-1002_6_bs=off:cond=on:drc=off:fde=none:nwc=1.5:sd=1:ss=included:sos=on:sagn=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_8");
	quick.push("dis-1002_16_bs=off:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off_3");
	quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_21");
	quick.push("ott+1_3:1_bd=off:bs=off:bsr=unit_only:ep=on:nwc=10:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=sat_10");
	quick.push("dis+10_8:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.1:nicw=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spl=sat:sp=reverse_arity_40");
	quick.push("ott+1011_3:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.5:sd=3:ss=axioms:sos=all:sio=off:spl=off_47");
	quick.push("dis-4_4:1_bs=off:ep=RST:gsp=input_only:gs=on:nwc=5:sd=1:ss=included:st=5.0:sos=on:sio=off:sfv=off:sp=occurrence_7");
	quick.push("dis+2_4_bs=off:cond=on:drc=off:ep=on:lcm=predicate:nwc=4:sd=1:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off:sp=occurrence_3");
	quick.push("ott+1_2_bs=off:drc=off:ep=on:nwc=3:nicw=on:sd=2:sgt=20:ss=axioms:sos=on:sagn=off:spl=sat:sser=off_55");
	quick.push("dis-1010_1024_bs=off:cond=fast:drc=off:fde=none:nwc=1:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_5");
	quick.push("dis+1011_1_bs=off:drc=off:nwc=1.2:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=2.0:ssnc=none_10");
	quick.push("dis-2_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=1.5:sd=3:sgt=10:ss=axioms:sos=on:spl=sat_36");
	quick.push("ott+2_3:1_bs=off:br=off:drc=off:nwc=1.1:nicw=on:sd=3:ss=axioms:st=3.0:sos=all:sio=off:spl=off:urr=on_13");
	quick.push("dis+2_8:1_bd=off:bs=off:bsr=on:drc=off:lcm=reverse:nwc=4:nicw=on:sd=3:sgt=5:ss=axioms:st=1.5:sos=on:spl=sat:sser=off:sp=reverse_arity_28");
	quick.push("ott+1_2:3_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=1.3:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_141");
	quick.push("dis+2_4_bs=off:drc=off:ep=RST:lcm=predicate:nwc=10:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off:sp=occurrence_24");
	quick.push("dis-10_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=4:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence_21");
	quick.push("ott+2_4:1_bd=off:bs=off:drc=off:gsp=input_only:nwc=1.1:nicw=on:sd=3:ss=axioms:sos=on:spl=sat:urr=on_23");
	quick.push("ott+10_2:3_bs=off:drc=off:gs=on:nwc=1.5:sd=2:ss=axioms:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:urr=on_53");
	quick.push("dis+11_3:1_bs=off:br=off:cond=on:drc=off:ep=on:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spl=sat:sser=off:urr=on_259");
	quick.push("dis+1_14_bd=off:bs=off:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=4:sos=on:sio=off:spo=on:sp=reverse_arity_114");
	quick.push("ott+11_2:1_bs=off:br=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:sd=2:ss=axioms:st=1.5:sos=all:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:urr=on_175");
	quick.push("dis+2_4_bs=off:drc=off:ep=RST:flr=on:lcm=reverse:nwc=1.5:sos=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sp=reverse_arity_179");
	quick.push("dis+2_1_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=1:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off_8");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=10:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_102");
      }
      else if (atoms > 2200) {
	quick.push("ott+1_3:1_bd=off:bs=off:bsr=unit_only:ep=on:nwc=10:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=sat_22");
	quick.push("ott+11_2:1_bs=off:br=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:sd=2:ss=axioms:st=1.5:sos=all:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:urr=on_5");
	quick.push("ott+1011_2:1_bs=off:cond=fast:drc=off:nwc=1:nicw=on:sos=all:sio=off:spo=on_29");
	quick.push("dis+1011_12_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_104");
	quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_205");
	quick.push("lrs-11_12_bs=off:drc=off:fde=none:gsp=input_only:gs=on:lcm=predicate:nwc=4:nicw=on:stl=300:sos=all:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sfv=off:sp=occurrence:urr=on:updr=off_1612");
      }
      else if (atoms > 900) {
	quick.push("lrs+1_5_bs=off:cond=fast:drc=off:flr=on:nwc=10:stl=30:sac=on:sio=off:urr=on_6");
	quick.push("ott+1_5:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=5:ss=axioms:sos=all_40");
	quick.push("ott-1002_5:1_bs=off:bsr=on:cond=fast:drc=off:gsp=input_only:nwc=2:sos=all:sio=off:spo=on:urr=on_2");
	quick.push("ott+1011_3:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.5:sd=3:ss=axioms:sos=all:sio=off:spl=off_47");
	quick.push("dis+1011_4_bs=off:drc=off:nwc=4:sgo=on_58");
	quick.push("dis+1010_2:3_bs=off:bsr=unit_only:drc=off:ep=on:fsr=off:fde=none:lcm=predicate:nwc=1.5:sos=on:sac=on:sio=off:spo=on:sp=occurrence_424");
	quick.push("ott+2_20_cond=fast:drc=off:flr=on:lcm=reverse:nwc=1.1:nicw=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_249");
	quick.push("ott-1010_4:1_bs=off:bsr=on:cond=on:drc=off:fde=none:gsp=input_only:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:ssfq=1.0:ssnc=none_287");
	quick.push("ott-1010_3_bd=off:bs=off:bsr=unit_only:drc=off:fde=none:nwc=1:nicw=on:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_325");
	quick.push("dis+2_4_bs=off:drc=off:ep=RST:lcm=predicate:nwc=10:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off:sp=occurrence_7");
	quick.push("ott+2_8:1_bs=off:bsr=on:drc=off:fde=none:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_36");
	quick.push("ott+1011_8:1_bs=off:drc=off:fde=none:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off:sp=occurrence_86");
      }
      else {
	quick.push("ott-1010_4:1_bs=off:bsr=on:cond=on:drc=off:fde=none:gsp=input_only:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:ssfq=1.0:ssnc=none_7");
	quick.push("dis+2_2:3_bs=off:bsr=unit_only:cond=fast:drc=off:ep=RS:lcm=reverse:nwc=1.2:sos=all:sio=off:spl=sat:ssfp=4000:ssfq=1.4:ssnc=none:sfv=off:sp=occurrence_24");
	quick.push("dis+1010_40_bs=off:drc=off:ep=RS:nwc=1:sio=off:spo=on:spl=sat:ssnc=none_21");
	quick.push("ott-1002_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1.1:sos=all:sio=off:spo=on:sp=occurrence_17");
	quick.push("ott+11_2:1_bs=off:cond=fast:drc=off:ep=RS:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=2.5:sio=off:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_23");
	quick.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=2.5:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_9");
	quick.push("ott+1_2:3_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=1.3:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_3");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=10:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_272");
	quick.push("dis-1010_5:4_bs=off:bsr=on:cond=fast:drc=off:fde=none:gsp=input_only:nwc=3:sgo=on:sio=off:sp=occurrence:urr=on_150");
	quick.push("ott+11_1_bs=off:drc=off:ep=RS:flr=on:fde=none:nwc=4:sos=all:sgo=on:sio=off_220");
	quick.push("lrs+11_4_cond=fast:drc=off:flr=on:lcm=reverse:nwc=10:stl=50:sos=on:sio=off:spl=sat:ssfp=100000:ssfq=1.4:ssnc=none:sp=reverse_arity_351");
	quick.push("dis-1002_3_bs=off:cond=on:drc=off:ep=RS:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none_18");
	quick.push("ott-1002_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ep=RST:flr=on:fde=none:lcm=reverse:nwc=10:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:urr=on_85");
      }
    }
    else if (prop == 131073) {
      if (atoms > 400) {
	quick.push("ott+11_1_bs=off:drc=off:ep=RS:flr=on:fde=none:nwc=4:sos=all:sgo=on:sio=off_2");
	quick.push("dis+1011_4_bs=off:drc=off:nwc=4:sgo=on_11");
	quick.push("dis+2_8:1_bd=off:bs=off:bsr=on:drc=off:lcm=reverse:nwc=4:nicw=on:sd=3:sgt=5:ss=axioms:st=1.5:sos=on:spl=sat:sser=off:sp=reverse_arity_12");
	quick.push("dis-10_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=4:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence_2");
	quick.push("dis-1010_2_bs=off:bsr=on:drc=off:nwc=4:ssac=none:sscc=on:ssfp=100000:ssfq=1.4:ssnc=all_4");
	quick.push("dis+1_128_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=10:sd=2:ss=included:st=2.0:sagn=off:sio=off:spl=sat:ssnc=none_3");
	quick.push("ins+10_2:3_bs=unit_only:flr=on:fde=none:igbrr=0.7:igrr=1/32:igrp=200:igrpq=1.0:igwr=on:lcm=predicate:nwc=1.7:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=off_26");
	quick.push("dis+1_3_bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sd=1:ss=included:st=2.0:sagn=off:sio=off:spl=sat:sser=off:ssnc=none_2");
	quick.push("dis+4_5_bs=off:drc=off:lcm=reverse:nwc=1.1:sos=all:sio=off:spl=sat:ssfp=40000:ssfq=1.4:ssnc=none:sp=occurrence_7");
	quick.push("ins-1003_7_bs=off:ep=RSTC:flr=on:igbrr=0.0:igrr=1/128:igrp=1400:igrpq=1.1:igwr=on:nwc=1.3:sos=on:sio=off:spl=off_2");
	quick.push("ott+11_2:1_bs=off:cond=fast:drc=off:ep=RS:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=2.5:sio=off:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_12");
	quick.push("dis+1011_12_bs=off:drc=off:nwc=5:nicw=on:sio=off:spl=sat:ssfq=1.2:ssnc=none_14");
	quick.push("ott+11_3:2_bs=off:cond=on:drc=off:ep=RSTC:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sagn=off:sio=off:spl=sat:urr=on_3");
	quick.push("dis+2_4_bs=off:br=off:drc=off:nwc=1.2:sd=2:ss=axioms:st=2.0:sio=off:urr=on_24");
	quick.push("ott-1010_2:3_bs=off:cond=fast:drc=off:nwc=1.7:sos=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_9");
	quick.push("dis+1010_32_cond=fast:drc=off:ep=RS:fsr=off:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_66");
	quick.push("lrs-1002_3_bd=off:bs=off:drc=off:ep=on:nwc=1.7:stl=150:sos=on:sac=on:sio=off_21");
	quick.push("tab+10_1_ep=RST:gsp=input_only:sd=4:ss=axioms:st=2.0:sio=off:tbsr=off:tgawr=1/32:tglr=1/5:tipr=off:tlawr=8/1_73");
	quick.push("ott+1011_3:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.5:sd=3:ss=axioms:sos=all:sio=off:spl=off_183");
	quick.push("ott-1002_5:1_bs=off:bsr=on:cond=fast:drc=off:gsp=input_only:nwc=2:sos=all:sio=off:spo=on:urr=on_122");
	quick.push("dis+1011_12_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_28");
	quick.push("ott+1011_5:4_bs=off:cond=fast:drc=off:flr=on:fsr=off:nwc=2:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_32");
	quick.push("dis+10_8:1_bs=off:br=off:cond=on:drc=off:ep=RST:fsr=off:nwc=1.3:sd=4:ss=axioms:st=3.0:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_92");
	quick.push("dis+2_1_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=1:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off_148");
	quick.push("lrs+1011_8_bd=off:bs=unit_only:bsr=on:drc=off:lcm=reverse:nwc=1:nicw=on:stl=270:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_1");
	quick.push("dis+11_4_bs=off:drc=off:ep=on:gsp=input_only:nwc=5:sgt=15:ss=axioms:sos=on:spl=sat_1");
	quick.push("dis-1010_7_bs=off:cond=fast:drc=off:fde=none:nwc=1.1:nicw=on:sd=1:ss=axioms:st=3.0:sio=off:spl=sat_2");
	quick.push("ott+10_8:1_bd=off:bs=off:cond=fast:drc=off:flr=on:nwc=1.3:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:urr=on_4");
	quick.push("ott+1011_64_bs=off:cond=fast:drc=off:gsp=input_only:nwc=1:ss=axioms:st=1.2:spl=sat:sser=off:urr=on_5");
	quick.push("dis+2_128_bs=off:drc=off:lcm=reverse:nwc=1.3:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_8");
	quick.push("dis-1002_6_bs=off:cond=on:drc=off:fde=none:nwc=1.5:sd=1:ss=included:sos=on:sagn=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_13");
	quick.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none_13");
	quick.push("dis-1010_64_bs=off:drc=off:nwc=2.5:nicw=on:sgo=on:sio=off:spo=on:sser=off:ssfp=40000:ssfq=1.0:ssnc=none_20");
      }
      else if (atoms > 150) {
	quick.push("ott-1010_2:3_bs=off:cond=fast:drc=off:nwc=1.7:sos=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_5");
	quick.push("dis+10_24_bs=off:br=off:drc=off:nwc=4:sd=5:ss=axioms:st=1.5:sgo=on:sio=off:spl=sat:ssac=none:ssfp=1000:ssfq=1.0:ssnc=all:urr=on_1");
	quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_20");
	quick.push("dis-1010_64_bs=off:drc=off:nwc=2.5:nicw=on:sgo=on:sio=off:spo=on:sser=off:ssfp=40000:ssfq=1.0:ssnc=none_2");
	quick.push("dis+1_2:3_bs=off:drc=off:lcm=predicate:nwc=3:nicw=on:ss=included:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off:sp=occurrence_25");
	quick.push("dis-1002_1024_bs=off:cond=on:drc=off:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_1");
	quick.push("dis-1010_2_bd=off:bs=off:cond=fast:drc=off:nwc=5:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off:sp=occurrence_27");
	quick.push("lrs-11_6_bs=off:bsr=unit_only:drc=off:gsp=input_only:lcm=predicate:nwc=10:stl=30:sos=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on:updr=off_11");
	quick.push("dis+1011_12_bs=off:drc=off:nwc=5:nicw=on:sio=off:spl=sat:ssfq=1.2:ssnc=none_68");
	quick.push("dis+2_4_bs=off:cond=on:drc=off:ep=on:lcm=predicate:nwc=4:sd=1:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off:sp=occurrence_19");
	quick.push("dis-1_3_bsr=unit_only:drc=off:lcm=reverse:nwc=4:sos=all:sac=on:sgo=on:sio=off:spo=on:sp=reverse_arity_146");
	quick.push("dis+1_24_bs=off:drc=off:ep=on:lcm=predicate:nwc=3:nicw=on:ss=included:st=5.0:sos=on:sagn=off:spl=sat:sser=off:ssnc=none_33");
	quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:gsp=input_only:nwc=1.3:nicw=on:sd=2:sgt=10:ss=axioms:sagn=off:spl=sat:sser=off_72");
	quick.push("ott+1_2:3_bs=off:cond=fast:drc=off:flr=on:lcm=predicate:nwc=1.3:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_20");
	quick.push("dis-1010_3:2_bs=off:drc=off:ep=on:nwc=3:sac=on:sgo=on:sio=off:spo=on:sfv=off_242");
	quick.push("ott+1010_5_bd=off:bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_189");
	quick.push("dis+2_16_bs=off:drc=off:ep=on:gsp=input_only:lcm=reverse:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none_420");
	quick.push("ott+1011_2_bs=off:drc=off:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:updr=off_227");
	quick.push("dis+2_2:3_bs=off:drc=off:lcm=reverse:nwc=2.5:sos=all:sser=off:ssfp=10000:ssfq=2.0:ssnc=all_231");
	quick.push("dis+2_4_bs=off:br=off:drc=off:nwc=1.2:sd=2:ss=axioms:st=2.0:sio=off:urr=on_1");
	quick.push("ott+1011_2:1_bs=off:cond=fast:drc=off:nwc=1:nicw=on:sos=all:sio=off:spo=on_23");
      }
      else {
	quick.push("lrs-1010_7_bs=unit_only:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1.7:stl=30:sgo=on:spo=on:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_1");
	quick.push("dis-1002_6_bs=off:drc=off:nwc=1.1:nicw=on:sd=1:ss=axioms:st=3.0:sio=off:spl=sat:sser=off_1");
	quick.push("ott+1_5:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=5:ss=axioms:sos=all_4");
	quick.push("ott+2_20_cond=fast:drc=off:flr=on:lcm=reverse:nwc=1.1:nicw=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_25");
	quick.push("lrs+1011_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1:nicw=on:stl=240:sos=all:sio=off:spo=on:ssac=none:ssfp=1000:ssfq=1.1:ssnc=all_dependent_1");
	quick.push("dis+1_2:3_bs=off:drc=off:lcm=predicate:nwc=3:nicw=on:ss=included:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off:sp=occurrence_97");
	quick.push("lrs+1011_8_bd=off:bs=unit_only:bsr=on:drc=off:lcm=reverse:nwc=1:nicw=on:stl=270:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_8");
	quick.push("dis+2_4_bs=off:cond=on:drc=off:ep=on:lcm=predicate:nwc=4:sd=1:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off:sp=occurrence_18");
	quick.push("lrs+10_20_bs=off:drc=off:nwc=1.1:nicw=on:stl=90:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_860");
	quick.push("ott-1002_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1.1:sos=all:sio=off:spo=on:sp=occurrence_26");
	quick.push("dis+1011_14_bd=off:bs=off:cond=fast:drc=off:nwc=4:sio=off:spl=sat:ssfq=1.0:ssnc=none_262");
      }
    }
    else if (prop == 2) {
      if (atoms > 25) {
	quick.push("ins-1010_1_bs=unit_only:drc=off:igbrr=0.0:igrr=1/4:igrp=4000:igrpq=1.0:igwr=on:nwc=1.1_16");
	quick.push("lrs+10_20_bs=off:drc=off:nwc=1.1:nicw=on:stl=90:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_874");
	quick.push("lrs+1_64_bs=off:drc=off:gsp=input_only:nwc=1.7:nicw=on:stl=60:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:updr=off_282");
	quick.push("ott+10_1024_bs=off:cond=on:drc=off:gsp=input_only:nwc=1.2:sio=off:spl=sat:ssfp=10000:ssnc=none:updr=off_368");
      }
      else {
	quick.push("ins+3_10_bs=off:drc=off:fde=none:igbrr=0.8:igrr=1/128:igrp=100:igrpq=1.0:igwr=on:nwc=2.5:sio=off:spl=off_152");
	quick.push("lrs+1_6_bs=off:drc=off:nwc=3:stl=360:sos=all:sio=off:spl=sat:ssac=none:sscc=on:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_48");
	quick.push("ott+1_5_bs=off:drc=off:nwc=4:sio=off:sp=occurrence_245");
	quick.push("ott+11_24_bs=off:cond=fast:drc=off:fde=none:gs=on:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=1.4:ssnc=none:sp=reverse_arity_178");
	quick.push("ott-1010_64_bs=off:br=off:drc=off:flr=on:gs=on:nwc=1:sac=on:sio=off:urr=on_577");
	quick.push("ott+4_14_bs=unit_only:cond=fast:drc=off:nwc=1.2:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_383");
	quick.push("ins-1010_1_bs=unit_only:drc=off:igbrr=0.0:igrr=1/4:igrp=4000:igrpq=1.0:igwr=on:nwc=1.1_73");
	quick.push("lrs+10_20_bs=off:cond=on:drc=off:gs=on:nwc=1.1:stl=10:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_80");
      }
    }
    else if (prop == 131072) {
      quick.push("dis-1010_2_bs=off:bsr=on:drc=off:nwc=4:ssac=none:sscc=on:ssfp=100000:ssfq=1.4:ssnc=all_16");
      quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_90");
      quick.push("dis+1_2:3_bs=off:drc=off:lcm=predicate:nwc=3:nicw=on:ss=included:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off:sp=occurrence_1");
      quick.push("dis-1002_16_bs=off:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off_7");
      quick.push("dis-1002_1024_bs=off:cond=on:drc=off:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_16");
      quick.push("dis-1010_2:3_bs=off:drc=off:nwc=3:sd=2:ss=axioms:st=1.5:sac=on:sio=off_105");
      quick.push("ott-1002_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1.1:sos=all:sio=off:spo=on:sp=occurrence_110");
      quick.push("dis+1003_1024_bs=off:drc=off:fsr=off:nwc=1.7:nicw=on:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none_38");
      quick.push("lrs+10_20_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:stl=80:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none_59");
      quick.push("ott+10_3:1_bd=off:drc=off:lcm=reverse:nwc=10:nicw=on:sio=off:spo=on:ssac=none:sscc=on:sser=off:ssfp=1000:ssfq=1.2:ssnc=all_667");
      quick.push("dis-1010_50_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_580");
      quick.push("ins-1010_1_bs=unit_only:drc=off:igbrr=0.0:igrr=1/4:igrp=4000:igrpq=1.0:igwr=on:nwc=1.1_12");
    }
    else if (atoms > 10000) {
      quick.push("ins+10_2:3_bs=unit_only:flr=on:fde=none:igbrr=0.7:igrr=1/32:igrp=200:igrpq=1.0:igwr=on:lcm=predicate:nwc=1.7:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=off_24");
      quick.push("dis+2_10_bs=off:cond=fast:ep=RST:lcm=reverse:nwc=1:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_44");
      quick.push("dis-1002_1024_bs=off:cond=on:drc=off:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_33");
      quick.push("dis+1_128_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=10:sd=2:ss=included:st=2.0:sagn=off:sio=off:spl=sat:ssnc=none_35");
      quick.push("ins-1003_7_bs=off:ep=RSTC:flr=on:igbrr=0.0:igrr=1/128:igrp=1400:igrpq=1.1:igwr=on:nwc=1.3:sos=on:sio=off:spl=off_6");
      quick.push("dis+1_10_bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sd=7:ss=axioms:st=1.5:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on_153");
      quick.push("dis+11_10_bs=off:lcm=predicate:nwc=1.3:sio=off_100");
      quick.push("dis+11_1024_bsr=unit_only:cond=fast:nwc=1.3:sio=off:spl=off_590");
      quick.push("ott+1_5_bs=off:drc=off:nwc=4:sio=off:sp=occurrence_217");
      quick.push("dis+11_32_bs=off:nwc=1.1:sio=off:spl=off:updr=off_244");
    }
    else if (prop == 131083) {
      quick.push("dis-1010_7_bs=off:cond=fast:drc=off:fde=none:nwc=1.1:nicw=on:sd=1:ss=axioms:st=3.0:sio=off:spl=sat_1");
      quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_6");
      quick.push("dis+2_128_bs=off:drc=off:lcm=reverse:nwc=1.3:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_2");
      quick.push("ott-1010_4:1_bs=off:bsr=on:cond=on:drc=off:fde=none:gsp=input_only:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:ssfq=1.0:ssnc=none_187");
      quick.push("dis+1010_1_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:nwc=1.5:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none_441");
      quick.push("lrs+10_20_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:stl=80:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none_474");
    }
    else if (prop == 131074) {
      quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_2");
      quick.push("dis-1010_2_bs=off:bsr=on:drc=off:nwc=4:ssac=none:sscc=on:ssfp=100000:ssfq=1.4:ssnc=all_23");
      quick.push("ott+1_5:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=5:ss=axioms:sos=all_4");
      quick.push("dis+10_2_bs=off:cond=on:drc=off:fde=none:lcm=predicate:nwc=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sp=reverse_arity_31");
      quick.push("lrs+1011_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1:nicw=on:stl=240:sos=all:sio=off:spo=on:ssac=none:ssfp=1000:ssfq=1.1:ssnc=all_dependent_75");
      quick.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_236");
      quick.push("dis-1010_64_bs=off:drc=off:nwc=2.5:nicw=on:sgo=on:sio=off:spo=on:sser=off:ssfp=40000:ssfq=1.0:ssnc=none_27");
      quick.push("dis+1011_4_bs=off:drc=off:nwc=4:sgo=on_56");
      quick.push("ott+4_40_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=5:nicw=on:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:spl=sat:sser=off:updr=off_157");
    }
    else {
      quick.push("ott+1011_10_bs=off:cond=on:drc=off:nwc=1.5:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_4");
      quick.push("ins+10_2:3_bs=off:cond=fast:ep=RSTC:igbrr=0.8:igrr=1/2:igrp=100:igrpq=1.0:igwr=on:nwc=2:sos=all:sio=off:urr=on_1");
      quick.push("dis+2_2:3_bs=off:drc=off:lcm=reverse:nwc=2.5:sos=all:sser=off:ssfp=10000:ssfq=2.0:ssnc=all_9");
      quick.push("dis+4_5:1_bs=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ss=axioms:st=2.0:sac=on:sio=off:sp=occurrence:urr=on_3");
      quick.push("dis+11_2:3_bs=off:bsr=unit_only:drc=off:ep=R:lcm=reverse:nwc=2:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_1");
      quick.push("dis+1011_28_cond=on:drc=off:nwc=5:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:updr=off_12");
      quick.push("dis+1011_12_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_1");
      quick.push("dis+1011_10_bs=off:drc=off:nwc=1.3:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off_37");
      quick.push("ins+1011_8:1_bs=off:cond=fast:drc=off:ep=on:igbrr=0.1:igrr=1/4:igrpq=1.0:igwr=on:nwc=1.3:sos=all:sio=off:sfv=off:urr=on:updr=off_8");
      quick.push("dis+1010_12_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:ssnc=none:sfv=off_1");
      quick.push("lrs-1010_7_bs=unit_only:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1.7:stl=30:sgo=on:spo=on:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_17");
      quick.push("dis+1011_14_bd=off:bs=off:cond=fast:drc=off:nwc=4:sio=off:spl=sat:ssfq=1.0:ssnc=none_7");
      quick.push("ott+11_1024_bd=off:bs=off:br=off:cond=fast:drc=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfq=1.2:ssnc=none:urr=on_128");
      quick.push("ott+1_5:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=5:ss=axioms:sos=all_40");
      quick.push("dis+11_1_bs=off:drc=off:ep=on:flr=on:lcm=predicate:nwc=5:nicw=on:ss=included:st=5.0:sos=all:sagn=off:spl=sat:sser=off:ssnc=none:updr=off_24");
      quick.push("dis+1010_2:3_bs=off:bsr=unit_only:drc=off:ep=on:fsr=off:fde=none:lcm=predicate:nwc=1.5:sos=on:sac=on:sio=off:spo=on:sp=occurrence_9");
      quick.push("dis-1010_3:2_bs=off:drc=off:ep=on:nwc=3:sac=on:sgo=on:sio=off:spo=on:sfv=off_8");
      quick.push("lrs+1011_8_bd=off:bs=unit_only:bsr=on:drc=off:lcm=reverse:nwc=1:nicw=on:stl=270:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_10");
      quick.push("dis+11_3:1_bs=off:br=off:cond=on:drc=off:ep=on:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spl=sat:sser=off:urr=on_48");
      quick.push("lrs+1011_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1:nicw=on:stl=240:sos=all:sio=off:spo=on:ssac=none:ssfp=1000:ssfq=1.1:ssnc=all_dependent_12");
      quick.push("dis+10_24_bs=off:br=off:drc=off:nwc=4:sd=5:ss=axioms:st=1.5:sgo=on:sio=off:spl=sat:ssac=none:ssfp=1000:ssfq=1.0:ssnc=all:urr=on_7");
      quick.push("dis+1011_2_bs=off:drc=off:nwc=1.1:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:sfv=off:urr=on_53");
      quick.push("dis-1002_8:1_bs=off:cond=on:drc=off:flr=on:gs=on:nwc=4:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:urr=on_2");
      quick.push("ins+2_4:1_bs=off:cond=on:ep=RSTC:gs=on:igbrr=0.4:igrr=1/128:igrpq=1.05:igwr=on:nwc=5:sos=on:sio=off:urr=on_1");
      quick.push("ott+1011_8:1_bs=off:drc=off:fde=none:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off:sp=occurrence_108");
      quick.push("dis-1010_7_bs=off:cond=fast:drc=off:fde=none:nwc=1.1:nicw=on:sd=1:ss=axioms:st=3.0:sio=off:spl=sat_165");
      quick.push("dis+1_24_bs=off:drc=off:ep=on:lcm=predicate:nwc=3:nicw=on:ss=included:st=5.0:sos=on:sagn=off:spl=sat:sser=off:ssnc=none_31");
      quick.push("ott+2_8:1_bs=off:bsr=on:drc=off:fde=none:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_23");
      quick.push("dis+1010_1_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:nwc=1.5:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none_118");
      quick.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_296");
      quick.push("ott+1011_64_bs=off:cond=fast:drc=off:gsp=input_only:nwc=1:ss=axioms:st=1.2:spl=sat:sser=off:urr=on_212");
      quick.push("dis+11_4_bs=off:drc=off:ep=on:gsp=input_only:nwc=5:sgt=15:ss=axioms:sos=on:spl=sat_164");
      quick.push("lrs+10_20_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:stl=80:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none_14");
      quick.push("lrs+11_4_cond=fast:drc=off:flr=on:lcm=reverse:nwc=10:stl=50:sos=on:sio=off:spl=sat:ssfp=100000:ssfq=1.4:ssnc=none:sp=reverse_arity_24");
    }
    break;

  case Property::FNE:
    if (atoms > 200) {
      quick.push("ins+10_1_gsp=input_only:igbrr=0.9:igrp=100:igrpq=1.1:nwc=2_5");
      quick.push("dis+11_50_bs=off:bsr=on:cond=on:lcm=reverse:nwc=1:sio=off:spl=sat:sser=off:ssnc=none:updr=off_267");
      quick.push("dis+4_128_bs=off:cond=on:flr=on:nwc=1.2:sos=on:sac=on_20");
      quick.push("dis+1011_3_bs=off:cond=fast:flr=on:gsp=input_only:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_59");
      quick.push("tab+10_1_spl=off:tbsr=off:tfsr=off:tgawr=3/1:tglr=1/20:tipr=off:tlawr=8/1_114");
      quick.push("dis+3_6_flr=on:fsr=off:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:sp=occurrence_34");
      quick.push("ott+1011_50_bs=off:gs=on:nwc=2.5:nicw=on:sio=off:spl=sat:ssnc=none:urr=on:updr=off_190");
      quick.push("ott+1_7_bs=off:bsr=unit_only:fsr=off:gsp=input_only:nwc=1.5:spo=on_354");
      quick.push("dis+1010_8_bs=off:nwc=1.1:sio=off_134");
      quick.push("dis+1004_10_bs=off:nwc=1.5:sagn=off:sio=off:spl=sat:ssnc=none_617");
    }
    else if (atoms > 120) {
      quick.push("ott-1002_3_bs=unit_only:bsr=unit_only:cond=on:gsp=input_only:nwc=1.2:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:urr=on_185");
      quick.push("dis+4_10_bs=off:cond=fast:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1.2:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence:updr=off_204");
      quick.push("lrs+1002_128_bs=off:cond=on:flr=on:lcm=reverse:nwc=1:stl=120:spo=on_990");
    }
    else {
      quick.push("dis+1011_3_bs=off:cond=fast:flr=on:gsp=input_only:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_1");
      quick.push("dis+4_10_bs=off:cond=fast:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1.2:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence:updr=off_1");
      quick.push("lrs+1002_128_bs=off:cond=on:flr=on:lcm=reverse:nwc=1:stl=120:spo=on_28");
      quick.push("ott+1_40_bsr=unit_only:cond=fast:gs=on:nwc=1.5:sio=off:spl=sat:ssnc=none:urr=on_102");
      quick.push("ins+10_1_igbrr=0.5:igrpq=1.2:nwc=1:sio=off_32");
      quick.push("ott+1_16_bs=off:bsr=unit_only:fsr=off:gsp=input_only:nwc=2.5_94");
      quick.push("ott-1010_128_bs=off:cond=on:lcm=predicate:nwc=1.3:urr=on_394");
      quick.push("ott+10_1024_bs=off:fsr=off:nwc=1.5:nicw=on:sio=off:spl=off_963");
    }
    break;
 
  case Property::EPR:
    if (prop == 131072) {
      quick.push("ott+10_1024_bs=off:br=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.2:ssnc=none:urr=on_158");
      quick.push("dis+10_1024_bs=off:cond=fast:fsr=off:lcm=predicate:nwc=3:sio=off:spl=off:sp=occurrence:urr=on_162");
    }
    else if (atoms > 2000) {
      quick.push("ott+2_20_bs=off:bsr=unit_only:nwc=5:nicw=on:sio=off:spl=sat:ssnc=none_119");
      quick.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_1935");
    }
    else if (atoms > 1300) {
      quick.push("dis-11_24_bs=off:cond=fast:drc=off:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:urr=on_1");
      quick.push("ott+10_1024_bs=off:br=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.2:ssnc=none:urr=on_148");
      quick.push("dis+10_1024_bs=off:cond=fast:fsr=off:lcm=predicate:nwc=3:sio=off:spl=off:sp=occurrence:urr=on_171");
      quick.push("ins+3_128_bs=off:br=off:drc=off:igbrr=0.1:igrr=32/1:igrp=2000:igrpq=2.0:igwr=on:nwc=3:sos=all:sio=off:urr=on_262");
      quick.push("ins+2_128_bs=unit_only:drc=off:fsr=off:igbrr=1.0:igrr=128/1:igrp=200:igrpq=2.0:igwr=on:lcm=predicate:nwc=2:sos=on:sio=off:sp=occurrence_277");
      quick.push("dis+1_40_bs=unit_only:bsr=unit_only:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none_560");
    }
    else if (atoms > 450) {
      quick.push("dis-10_5:4_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=1.1:sac=on:sio=off:spo=on_5");
      quick.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_22");
      quick.push("ins+11_50_bs=off:cond=fast:drc=off:flr=on:gsp=input_only:igbrr=0.7:igrr=1/8:igrp=2000:igrpq=1.5:igwr=on:nwc=1.2:urr=on_56");
      quick.push("ins+3_50_bs=off:br=off:drc=off:igbrr=0.7:igrr=1/128:igrp=100:igrpq=1.05:igwr=on:lcm=predicate:nwc=2:sp=occurrence:urr=on_501");
      quick.push("ins+10_1_igbrr=0.4:igrp=200:igrpq=1.5:nwc=1.1:sio=off_561");
    }
    else {
      quick.push("ins+11_50_bs=off:cond=fast:drc=off:flr=on:gsp=input_only:igbrr=0.7:igrr=1/8:igrp=2000:igrpq=1.5:igwr=on:nwc=1.2:urr=on_12");
      quick.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_13");
      quick.push("ins+3_14_bs=off:cond=on:drc=off:flr=on:igbrr=0.2:igrr=1/128:igrp=200:igrpq=1.2:igwr=on:nwc=1:urr=on_43");
      quick.push("ott+1_128_bs=off:cond=fast:nwc=2.5:nicw=on:sio=off:spl=sat:ssnc=none:urr=on_1");
      quick.push("dis+4_10_bs=off:drc=off:fsr=off:nwc=5:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=1.0:ssnc=none_482");
      quick.push("ins-10_14_bs=off:drc=off:fde=none:igbrr=0.9:igrr=1/4:igrp=2000:igrpq=2.0:igwr=on:nwc=1.5:sos=on:sgo=on:sio=off:updr=off_1506");
    }
    break;
 
  case Property::UEQ:
    if (prop == 2048) {
      quick.push("dis+2_14_bs=off:br=off:ep=RSTC:flr=on:fsr=off:nwc=2.5:nicw=on:sos=all:sio=off:spl=sat:ssnc=none:urr=on_2");
      quick.push("dis+10_32_bs=off:drc=off:fsr=off:nwc=5_2");
      quick.push("lrs+10_14_drc=off:fde=none:nwc=2.5:stl=180_1097");
    }
    else if (prop == 2) {
      if (atoms <= 17) {
	quick.push("dis+11_16_bs=off:bfnt=on:fsr=off:fde=none:gs=on:nwc=1.3:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none_1");
	quick.push("ott+10_20_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.3:sp=occurrence_290");
	quick.push("ott+10_50_bs=off:drc=off:fsr=off:fde=none:nwc=1_213");
	quick.push("ott+10_8:1_bs=off:bsr=on:nwc=4_77");
	quick.push("lrs+10_20_bd=off:bs=unit_only:drc=off:fsr=off:nwc=1.2:stl=90_442");
	quick.push("ott+10_64_drc=off:nwc=1.1_298");
      }
      else if (atoms <= 20) {
	quick.push("ott+2_10_bs=off:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:nwc=1.7:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfq=1.1:ssnc=none_111");
	quick.push("lrs+10_2:1_bs=off:drc=off:fsr=off:nwc=2.5:stl=60:sp=occurrence_14");
	quick.push("lrs+10_14_drc=off:fde=none:nwc=2.5:stl=180_149");
	quick.push("ott+10_2_bs=off:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.2:sp=reverse_arity_158");
	quick.push("ott+10_50_bs=off:drc=off:fsr=off:fde=none:nwc=1_275");
	quick.push("ins+3_2_bs=off:bfnt=on:br=off:cond=on:fsr=off:fde=none:igbrr=0.9:igrr=1/64:igrpq=2.0:igwr=on:nwc=10:sio=off:urr=on_900");
      }
      else {
	quick.push("lrs+10_2:3_bs=unit_only:cond=on:drc=off:ep=on:fsr=off:gs=on:nwc=1:stl=20:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=occurrence_61");
	quick.push("lrs+10_8_bs=off:cond=fast:drc=off:fsr=off:gsp=input_only:gs=on:nwc=2:stl=120:urr=on_1148");
      }
    }
    else if (atoms <= 2) {
      quick.push("ott+2_10_bs=off:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:nwc=1.7:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfq=1.1:ssnc=none_17");
      quick.push("dis+10_12_bs=off:bsr=unit_only:fsr=off:nwc=2_1");
      quick.push("ins+4_8_bs=off:bfnt=on:br=off:cond=fast:flr=on:fsr=off:igbrr=0.1:igrr=1/128:igrp=100:igrpq=2.0:igwr=on:nwc=1.3:sos=all:urr=on_1");
      quick.push("ott+10_7_bd=off:bs=off:drc=off:fsr=off:fde=none:nwc=1.1:sp=occurrence_87");
      quick.push("lrs+10_1024_nwc=4:stl=150_1463");
    }
    else if (atoms <= 9) {
      quick.push("ott+11_20_bs=off:bfnt=on:cond=fast:fsr=off:lcm=predicate:nwc=2.5:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity_1");
      quick.push("dis+4_5:1_bs=off:br=off:ep=RSTC:fsr=off:nwc=3:sos=all:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on_3");
      quick.push("dis+10_12_bs=off:bsr=unit_only:fsr=off:nwc=2_1");
      quick.push("lrs+10_14_drc=off:fde=none:nwc=2.5:stl=180_852");
      quick.push("ins+3_2_bs=off:bfnt=on:br=off:cond=on:fsr=off:fde=none:igbrr=0.9:igrr=1/64:igrpq=2.0:igwr=on:nwc=10:sio=off:urr=on_33");
      quick.push("ott+10_5_bd=off:drc=off:nwc=2.5_761");
      quick.push("dis+10_12_bs=off:br=off:ep=RSTC:fsr=off:nwc=4:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none:urr=on_59");
    }
    else if (atoms <= 10) {
      quick.push("dis+11_16_bs=off:bfnt=on:fsr=off:fde=none:gs=on:nwc=1.3:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none_1");
      quick.push("ott+10_7_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.5_480");
      quick.push("ott+10_8:1_bs=off:drc=off:fsr=off:nwc=1.7_328");
      quick.push("ott+10_2:1_drc=off:nwc=5_1146");
      quick.push("ott+10_2:3_drc=off:nwc=2_504");
      quick.push("ott+10_8:1_nwc=3:sfv=off_860");
    }
    else if (atoms <= 15) {
      quick.push("ott+11_20_bs=off:bfnt=on:cond=fast:fsr=off:lcm=predicate:nwc=2.5:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity_1");
      quick.push("lrs+10_14_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.2:stl=20:sio=off:sp=occurrence_25");
      quick.push("lrs+3_20_bs=off:drc=off:fsr=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=3:stl=120_313");
      quick.push("ins+3_2_bs=off:bfnt=on:br=off:cond=on:fsr=off:fde=none:igbrr=0.9:igrr=1/64:igrpq=2.0:igwr=on:nwc=10:sio=off:urr=on_619");
      quick.push("ott+10_20_bd=off:drc=off:nwc=2:sp=occurrence_451");
    }
    else if (atoms <= 18) {
      quick.push("lrs+10_16_drc=off:nwc=1.2:stl=40_351");
      quick.push("dis+10_128_bs=unit_only:bsr=on:drc=off:fsr=off:nwc=2.5_295");
      quick.push("ott+10_8:1_bs=off:drc=off:fsr=off:nwc=1.7_275");
      quick.push("ott+10_10_drc=off:fde=none:nwc=1.1:sp=occurrence_363");
    }
    else {
      quick.push("lrs+10_16_drc=off:nwc=1.2:stl=40_391");
      quick.push("lrs+10_5:1_nwc=1:stl=90_214");
      quick.push("ott+10_2_fde=none:nwc=2.5:sp=reverse_arity_728");
    }
    break;
  }

  switch (cat) {
  case Property::NEQ:
    fallback.push("dis-1010_6_bs=off:drc=off:ep=on:gsp=input_only:nwc=10:nicw=on:sos=all:sp=occurrence_300");
    fallback.push("ott+11_2:3_bs=off:drc=off:flr=on:lcm=predicate:nwc=2.5:sio=off:spl=sat:sser=off:ssfp=100000:ssnc=none:sp=occurrence_300");
    fallback.push("dis+10_5_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=5:nicw=on:sgo=on:sio=off:sp=occurrence_100");
    fallback.push("dis+1011_6_bs=off:drc=off:ep=on:fde=none:nwc=1.1:sio=off:spl=sat:sser=off:ssnc=none_300");
    fallback.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_300");
    fallback.push("dis+11_64_bs=off:drc=off:fde=none:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence_300");
    fallback.push("ott+10_4:1_bd=off:bs=off:bsr=unit_only:drc=off:nwc=2:nicw=on:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on:updr=off_300");
    fallback.push("dis+11_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_300");
    fallback.push("ott-1010_2:1_bs=off:cond=fast:drc=off:nwc=3:sd=1:ss=axioms:st=2.0:sio=off:spl=sat:sser=off:ssnc=none_300");
    fallback.push("lrs+10_1_bs=off:cond=fast:nwc=5:sio=off:spl=sat:ssfq=1.1:ssnc=none_200");
    fallback.push("ott+11_3_bd=off:bs=off:drc=off:ep=on:flr=on:nwc=1:sio=off:spl=sat:ssfq=1.1:ssnc=none:sfv=off_300");
    fallback.push("dis-11_10_bfnt=on:cond=fast:lcm=predicate:nwc=1.2:sio=off:spl=off:sp=occurrence_600");
    fallback.push("dis+11_4:1_bs=off:drc=off:gsp=input_only:nwc=3:sos=on_300");
    fallback.push("dis+10_8:1_bs=off:br=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=1:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_300");
    fallback.push("dis+2_24_bs=off:cond=fast:drc=off:fsr=off:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=2.0:ssnc=none_300");
    fallback.push("dis+11_4:1_bs=off:cond=fast:drc=off:nwc=10:sio=off:spl=sat:sser=off:ssnc=none_300");
    fallback.push("ott+1_1024_bs=off:br=off:cond=on:drc=off:flr=on:gs=on:nwc=2.5:nicw=on:sd=1:ss=axioms:st=1.2:sac=on:sio=off:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=all_dependent:urr=on:updr=off_300");
    fallback.push("dis+1_40_bs=off:ep=RSTC:nwc=1.1:sio=off:spl=sat:sser=off:ssnc=none:urr=on_300");
    fallback.push("ott+1011_3_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.2:sio=off:spl=sat:ssfq=1.4:ssnc=none_300");
    fallback.push("dis+1011_24_cond=fast:drc=off:nwc=10:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_300");
    fallback.push("ott+11_3:1_bs=off:drc=off:ep=on:nwc=2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_300");
    fallback.push("lrs+2_3:1_bs=off:br=off:cond=fast:drc=off:flr=on:nwc=4:sio=off:spo=on:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=reverse_arity:urr=on_600");
    fallback.push("dis-11_28_bs=off:drc=off:flr=on:lcm=predicate:nwc=1.7:sos=on:sio=off:spl=sat:ssfq=1.0:ssnc=none_300");
    fallback.push("ins-1010_8:1_bs=off:ep=RSTC:fsr=off:igbrr=1.0:igrr=1/128:igrp=700:igrpq=1.5:igwr=on:nwc=3:sos=on:sgo=on:sio=off_300");
    fallback.push("ott+11_2_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:ep=on:fde=none:lcm=reverse:nwc=1.2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_300");
    fallback.push("dis+4_8:1_bs=off:drc=off:ep=RS:nwc=2:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=sat:sscc=on:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_200");
    fallback.push("lrs+1011_14_bd=off:bs=off:cond=on:drc=off:ep=on:lcm=predicate:nwc=1.7:sio=off:spo=on:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:urr=on_600");
    fallback.push("ott+11_8:1_drc=off:ep=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssnc=none:sp=occurrence:updr=off_600");
    fallback.push("dis+1011_2_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on:updr=off_300");
    fallback.push("ott+11_50_bd=off:bs=off:drc=off:ep=on:lcm=reverse:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssnc=none:sfv=off_300");
    fallback.push("lrs+2_64_bd=off:bs=off:br=off:cond=on:drc=off:flr=on:fde=none:nwc=1.7:sio=off:spl=sat:ssfp=1000:ssfq=1.4:ssnc=none:urr=on_300");
    fallback.push("dis+10_3:1_bs=off:bfnt=on:cond=on:lcm=predicate:nwc=1:nicw=on:sac=on:sio=off:spl=sat:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("dis-1002_5:1_bs=off:cond=fast:drc=off:ep=on:nwc=1.1:sd=4:ss=axioms:sos=on:sio=off:spl=sat:urr=on_300");
    fallback.push("ott+3_8:1_bd=off:bs=off:bsr=unit_only:drc=off:fsr=off:nwc=2.5:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=1.0:ssnc=none:updr=off_300");
    fallback.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=1.0:igrp=400:igrpq=1.5:nwc=5:sio=off_300");
    fallback.push("dis+10_1024_bs=off:drc=off:flr=on:fsr=off:nwc=1.1:sio=off:spl=sat:ssfq=1.4:ssnc=none_300");
    fallback.push("dis+1_8:1_bs=off:drc=off:lcm=reverse:nwc=1.5:sos=all:sio=off:spl=sat:ssfq=2.0:ssnc=none:sfv=off_300");
    fallback.push("dis+2_4:1_bs=unit_only:cond=on:flr=on:lcm=predicate:nwc=1:ssac=none:ssfp=100000:ssfq=2.0:ssnc=all:sfv=off:urr=on_300");
    fallback.push("dis-11_1024_bs=off:bfnt=on:lcm=predicate:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:sp=occurrence:urr=on_300");
    fallback.push("dis+1011_10_bs=off:drc=off:fsr=off:nwc=10:sos=on:sio=off:spl=sat:ssnc=none_300");
    fallback.push("dis+10_10_bs=off:cond=fast:drc=off:gs=on:nwc=1.7:nicw=on:sd=1:ss=axioms:st=3.0_300");
    fallback.push("dis+11_4_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=1.7:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_300");
    fallback.push("ins+2_5_bs=off:cond=fast:ep=RSTC:flr=on:gs=on:igbrr=0.7:igrr=1/4:igrp=700:igrpq=1.2:igwr=on:lcm=reverse:nwc=2:sio=off:urr=on_300");
    fallback.push("ott+1011_3_bs=off:bsr=unit_only:fde=none:nwc=2:sio=off:spl=sat:ssfq=1.0:ssnc=none_300");
    fallback.push("lrs+1010_24_bd=off:bs=off:cond=on:drc=off:gsp=input_only:nwc=1.3:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfq=1.0:ssnc=none:updr=off_100");
    fallback.push("dis+3_8:1_bs=off:drc=off:fsr=off:fde=none:nwc=10:sio=off:spl=sat:ssfp=10000:ssfq=1.4:ssnc=none:sp=reverse_arity_300");
    fallback.push("dis-1_128_bfnt=on:fsr=off:nwc=1.5:nicw=on:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=1.2:ssnc=all_500");
    fallback.push("lrs+2_14_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:nwc=1.1:sio=off:spl=sat:ssac=none:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence:updr=off_300");
    fallback.push("dis-1002_3:2_bs=off:cond=fast:drc=off:ep=RST:flr=on:fde=none:lcm=predicate:nwc=10:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:updr=off_300");
    fallback.push("dis+11_8:1_bs=off:drc=off:ep=RS:nwc=10:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_300");
    fallback.push("ott+10_2_bd=off:bs=off:drc=off:flr=on:fsr=off:nwc=1.7:sio=off:spl=sat:ssfq=2.0:ssnc=none_300");
    fallback.push("ott+10_28_bd=off:bs=off:drc=off:nwc=1.5:sio=off:spl=sat:ssnc=none_300");
    fallback.push("ott-11_2:3_bs=off:drc=off:fsr=off:lcm=predicate:nwc=5:nicw=on:sac=on:sio=off:spo=on:sp=reverse_arity_300");
    fallback.push("ott-11_40_bd=off:bs=off:drc=off:flr=on:fsr=off:lcm=predicate:nwc=10:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:updr=off_300");
    fallback.push("dis+3_4_bs=off:br=off:cond=on:drc=off:ep=RSTC:nwc=4:nicw=on:sos=all:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:urr=on_100");
    fallback.push("ins+1_3:1_bs=off:cond=on:ep=RSTC:flr=on:gs=on:igbrr=0.8:igrr=1/4:igrp=400:igrpq=1.1:igwr=on:nwc=1.5:sio=off:urr=on_300");
    fallback.push("lrs+2_3_bd=off:cond=on:drc=off:flr=on:nwc=1.3:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off:sp=reverse_arity_300");
    fallback.push("ott+11_2_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sp=reverse_arity_300");
    fallback.push("dis+11_20_bs=off:cond=fast:fde=none:lcm=reverse:nwc=3:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=reverse_arity_300");
    fallback.push("dis+11_4_ep=on:fde=none:lcm=reverse:nwc=10:sos=on:sio=off:spl=sat:ssnc=none_300");
    fallback.push("ott+1_10_bd=off:bs=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_300");
    fallback.push("dis+1011_1024_bs=unit_only:cond=fast:lcm=reverse:nwc=1.1:sos=on:sio=off:spl=sat:sser=off:ssnc=none:sfv=off_300");
    fallback.push("dis+10_1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:sos=on:sio=off:spl=sat:sser=off:ssnc=none_300");
    fallback.push("dis+1002_4:1_bs=off:cond=fast:drc=off:ep=RST:nwc=3:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_300");
    fallback.push("ott+10_64_bd=off:bs=off:drc=off:flr=on:gsp=input_only:lcm=predicate:nwc=2:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_300");
    fallback.push("dis+1011_64_bs=off:drc=off:ep=on:flr=on:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_300");
    fallback.push("ott+11_8:1_bs=off:drc=off:flr=on:lcm=predicate:nwc=2:sos=all:sio=off:spo=on:sfv=off_200");
    fallback.push("dis-1002_12_bs=off:cond=on:drc=off:ep=on:gsp=input_only:nwc=10:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_300");
    fallback.push("dis+1011_1024_bs=unit_only:drc=off:gsp=input_only:nwc=1.1:sio=off:spo=on:urr=on_300");
    fallback.push("dis+1_2:1_bs=off:bsr=on:cond=fast:ep=RSTC:gs=on:lcm=predicate:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence:urr=on_900");
    fallback.push("lrs+4_24_bd=off:bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sio=off:spl=sat:ssfp=4000:ssfq=1.2:ssnc=none_600");
    break;

  case Property::HEQ:
    fallback.push("lrs+11_2:1_bs=off:cond=on:drc=off:nwc=10:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_600");
    fallback.push("ins+4_12_bs=off:bfnt=on:cond=fast:gsp=input_only:igbrr=0.8:igrr=128/1:igrpq=2.0:nwc=1_300");
    fallback.push("ott+11_128_bs=off:drc=off:gsp=input_only:gs=on:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.4:ssnc=none:sp=occurrence_900");
    fallback.push("ott+11_16_bfnt=on:cond=fast:nwc=1.1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=1000:ssfq=2.0:sp=reverse_arity_1200");
    fallback.push("lrs+2_4_bs=off:cond=fast:drc=off:gsp=input_only:nwc=4:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none_900");
    fallback.push("dis+2_8_bd=off:bs=off:ep=RST:fsr=off:lcm=reverse:nwc=10:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off_300");
    fallback.push("dis+11_5:4_bs=off:cond=fast:drc=off:fde=none:nwc=1:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.2:ssnc=none:urr=on_300");
    fallback.push("ins+11_64_bs=off:cond=on:drc=off:fde=none:igbrr=0.2:igrr=1/64:igrp=400:igrpq=1.05:igwr=on:nwc=1.2:sio=off_900");
    fallback.push("ott+2_16_bsr=unit_only:br=off:cond=on:flr=on:fsr=off:nwc=5:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.1:ssnc=none:sfv=off:urr=on:updr=off_900");
    fallback.push("dis+2_1024_bd=off:bs=off:cond=fast:fsr=off:nwc=1:sio=off:spl=off_900");
    fallback.push("lrs+11_3:1_bs=unit_only:drc=off:fde=none:nwc=10:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none_600");
    fallback.push("dis+10_1024_bd=off:bs=off:cond=on:drc=off:fde=none:nwc=2.5:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:urr=on_300");
    fallback.push("dis+10_2:3_bfnt=on:cond=on:fsr=off:lcm=predicate:nwc=1:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=1.4:sp=reverse_arity_100");
    fallback.push("lrs-1_2_bs=off:drc=off:nwc=4:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none_300");
    fallback.push("dis-1002_3_bs=off:cond=fast:drc=off:nwc=10:nicw=on:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_300");
    fallback.push("dis+3_1024_bfnt=on:cond=fast:fsr=off:nwc=5:sio=off:spl=off_100");
    fallback.push("ott+11_24_bd=off:bs=off:drc=off:nwc=3:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none_300");
    fallback.push("ins+4_5:4_bs=off:br=off:cond=on:ep=RSTC:flr=on:fsr=off:igbrr=0.1:igrr=1/16:igrpq=1.0:igwr=on:nwc=2:urr=on_600");
    fallback.push("ins+2_64_bs=off:cond=on:drc=off:flr=on:fde=none:igbrr=0.1:igrr=1/16:igrpq=1.3:igwr=on:nwc=1.7:sp=reverse_arity_1200");
    break;

  case Property::PEQ:
   fallback.push("lrs+3_40_bs=unit_only:bsr=on:cond=on:drc=off:fsr=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfq=1.2:ssnc=none:urr=on:updr=off_1000");
    fallback.push("dis-3_28_bd=off:cond=on:nwc=1.5:sio=off_600");
    fallback.push("ott+11_5_bs=off:cond=fast:drc=off:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=1.2:ssnc=none_900");
    fallback.push("dis+10_64_bd=off:cond=fast:drc=off:nwc=3:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.1:ssnc=none_300");
    fallback.push("dis+1_1024_nwc=1.1:sio=off:spl=off:updr=off_400");
    fallback.push("ins+1_8:1_bs=off:bfnt=on:igbrr=0.8:igrr=2/1:igrpq=1.2:igwr=on:nwc=3:sos=all:sgo=on_300");
    fallback.push("dis-1003_128_drc=off:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none_300");
    fallback.push("lrs+10_2:3_bd=off:cond=on:drc=off:flr=on:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_900");
    fallback.push("lrs+3_4_bsr=unit_only:drc=off:fsr=off:nwc=1:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:urr=on_1500");
    fallback.push("dis+2_7_bd=off:drc=off:flr=on:fsr=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sfv=off_600");
    fallback.push("ins+1_20_bsr=on:br=off:cond=fast:drc=off:fsr=off:fde=none:igbrr=0.3:igrr=1/32:igrp=4000:igrpq=2.0:igwr=on:lcm=reverse:nwc=1.2:sgo=on:sio=off:sp=occurrence:urr=on_400");
    fallback.push("dis+1_2_bd=off:bs=off:drc=off:flr=on:fsr=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_300");
    fallback.push("ott+2_20_bs=off:cond=fast:drc=off:fde=none:nwc=2:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=none:sp=occurrence_300");
    fallback.push("ott+3_4:1_bsr=unit_only:cond=on:drc=off:fsr=off:fde=none:gs=on:nwc=1:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence:urr=on_300");
    fallback.push("lrs-1_128_bs=off:cond=fast:ep=on:nwc=1.2:nicw=on:sac=on:sio=off_300");
    fallback.push("dis-1004_1024_bs=off:cond=fast:drc=off:nwc=1.3:sio=off:spl=sat:ssfq=1.4:ssnc=none_300");
    fallback.push("ott+11_2:3_bd=off:drc=off:nwc=4:nicw=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:updr=off_300");
    fallback.push("ott+3_128_bs=off:drc=off:nwc=1.1:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:sp=occurrence_600");
    fallback.push("dis+11_32_bd=off:bsr=on:fsr=off:nwc=1.2:nicw=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.4:ssnc=none_600");
    fallback.push("ins+10_1_bfnt=on:igbrr=0.8:igrp=400:igrpq=2.0:nwc=1.7:sio=off_1500");
    fallback.push("lrs+4_14_cond=on:drc=off:flr=on:nwc=3:spl=sat:sser=off:ssnc=none_1800");
    break;

  case Property::EPR:
    fallback.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_2100");
    fallback.push("dis-10_5:4_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=1.1:sac=on:sio=off:spo=on_300");
    fallback.push("ott+10_1024_bs=off:br=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.2:ssnc=none:urr=on_300");
    fallback.push("ins+3_50_bs=off:br=off:drc=off:igbrr=0.7:igrr=1/128:igrp=100:igrpq=1.05:igwr=on:lcm=predicate:nwc=2:sp=occurrence:urr=on_600");
    fallback.push("ins+11_50_bs=off:cond=fast:drc=off:flr=on:gsp=input_only:igbrr=0.7:igrr=1/8:igrp=2000:igrpq=1.5:igwr=on:nwc=1.2:urr=on_300");
    fallback.push("dis+1_40_bs=unit_only:bsr=unit_only:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none_900");
    fallback.push("dis+10_1024_bs=off:cond=fast:fsr=off:lcm=predicate:nwc=3:sio=off:spl=off:sp=occurrence:urr=on_300");
    fallback.push("dis-11_24_bs=off:cond=fast:drc=off:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:urr=on_300");
    fallback.push("ins+2_128_bs=unit_only:drc=off:fsr=off:igbrr=1.0:igrr=128/1:igrp=200:igrpq=2.0:igwr=on:lcm=predicate:nwc=2:sos=on:sio=off:sp=occurrence_300");
    fallback.push("ins+3_128_bs=off:br=off:drc=off:igbrr=0.1:igrr=32/1:igrp=2000:igrpq=2.0:igwr=on:nwc=3:sos=all:sio=off:urr=on_300");
    fallback.push("ins+3_14_bs=off:cond=on:drc=off:flr=on:igbrr=0.2:igrr=1/128:igrp=200:igrpq=1.2:igwr=on:nwc=1:urr=on_300");
    fallback.push("ott+2_20_bs=off:bsr=unit_only:nwc=5:nicw=on:sio=off:spl=sat:ssnc=none_300");
    fallback.push("ins-10_14_bs=off:drc=off:fde=none:igbrr=0.9:igrr=1/4:igrp=2000:igrpq=2.0:igwr=on:nwc=1.5:sos=on:sgo=on:sio=off:updr=off_1800");
    break;

  case Property::HNE: 
    fallback.push("ott+4_6_bs=off:bsr=unit_only:cond=fast:nwc=3:nicw=on:sio=off:spl=sat:ssnc=none_300");
    fallback.push("dis+1011_20_bs=off:fsr=off:nwc=2:sio=off:spl=off_300");
    fallback.push("ott+11_8_bs=off:bfnt=on:cond=fast:nwc=1:sio=off:spl=sat:sser=off:ssfp=100000:ssnc=none_300");
    fallback.push("lrs+10_3:2_bs=off:cond=fast:nwc=10:sio=off:spo=on_900");
    fallback.push("lrs+1_128_bs=off:cond=on:gs=on:nwc=4:nicw=on:sio=off_900");
    fallback.push("dis+11_24_bs=off:cond=fast:nwc=1.3:nicw=on:sac=on:sio=off_300");
    fallback.push("dis-11_8:1_bs=off:nwc=2.5:sio=off:spl=off_300");
    fallback.push("ott+1003_28_bs=off:cond=on:flr=on:fsr=off:lcm=predicate:nwc=1:nicw=on:sio=off:spl=off_300");
    fallback.push("lrs+3_4_bs=off:cond=fast:flr=on:nwc=1:nicw=on:sio=off:spl=sat:ssnc=none_300");
    fallback.push("dis+11_2:3_bs=off:cond=fast:fsr=off:nwc=10:sio=off:spl=sat:sser=off:ssnc=none_300");
    fallback.push("dis+2_5:4_cond=fast:flr=on:lcm=predicate:nwc=1.5:sio=off:spl=off_600");
    fallback.push("lrs+1011_64_bs=unit_only:bsr=unit_only:cond=fast:flr=on:nwc=1:sio=off:spl=sat:ssfq=2.0_1800");
    fallback.push("dis+10_4_bs=off:nwc=5:sac=on:sio=off_200");
    fallback.push("lrs+11_128_cond=fast:lcm=reverse:nwc=1.5:nicw=on:sio=off:spl=sat:ssfp=100000:ssfq=2.0:ssnc=none_600");
    fallback.push("ott+1_8:1_bs=off:cond=on:gs=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssnc=none_300");
    fallback.push("lrs+10_8:1_bs=off:cond=fast:flr=on:fsr=off:nwc=2.5:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_900");
    fallback.push("dis+1002_64_bs=off:fsr=off:gsp=input_only:lcm=predicate:nwc=1.2:nicw=on:sio=off:spo=on_600");
    break;

  case Property::NNE: 
    fallback.push("dis+1011_12_bs=off:cond=fast:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.0:ssnc=none_900");
    fallback.push("ins+11_12_bs=off:bfnt=on:gsp=input_only:igbrr=0.9:igrr=4/1:igrp=400:igrpq=2.0:nwc=4_300");
    fallback.push("dis-1010_14_bsr=on:cond=on:nwc=1.5:sio=off:spl=sat:ssfp=100000:ssfq=1.1:ssnc=none_300");
    fallback.push("ott+1_20_bfnt=on:cond=on:nwc=3:sac=on:sgo=on:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.4_300");
    fallback.push("dis+1011_16_bs=unit_only:cond=on:fsr=off:gsp=input_only:nwc=1.7:sos=all:sgo=on:sio=off:spl=sat:ssfq=2.0:ssnc=all_200");
    fallback.push("dis-11_40_bs=off:lcm=predicate:nwc=1.2:sio=off:spl=sat:ssac=none:ssfp=40000:ssfq=2.0:ssnc=none_300");
    fallback.push("ott+4_2:1_bs=off:cond=on:lcm=predicate:nwc=10:nicw=on:sac=on:sio=off_300");
    fallback.push("dis-1_16_bs=off:bfnt=on:cond=on:lcm=predicate:nwc=1.2:nicw=on:ssfq=1.1:ssnc=none:sp=occurrence_100");
    fallback.push("dis+1_28_bs=off:bfnt=on:cond=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1.7:sio=off:spl=off:sp=occurrence_300");
    fallback.push("ott-3_16_bs=off:gsp=input_only:nwc=2:nicw=on:sos=all:sio=off:spl=sat:ssnc=none_300");
    fallback.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=0.7:igrpq=2.0:nwc=4_500");
    fallback.push("dis+11_128_bs=off:cond=fast:flr=on:lcm=reverse:nwc=2:sio=off:spl=sat:ssnc=none_300");
    fallback.push("dis+1011_128_bs=off:cond=fast:flr=on:fsr=off:lcm=reverse:nwc=2.5:nicw=on:sio=off:spl=sat:ssnc=none_300");
    fallback.push("ott-1002_1024_cond=on:flr=on:gs=on:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.1:ssnc=none:urr=on_300");
    fallback.push("dis+1011_50_bs=off:cond=fast:flr=on:gsp=input_only:nwc=1.3:sos=all_300");
    fallback.push("dis+4_12_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_300");
    fallback.push("dis+1011_40_bs=off:gsp=input_only:nwc=4:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_300");
    fallback.push("ott+1011_5_bs=off:gs=on:nwc=2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssnc=none_100");
    fallback.push("dis-2_16_bs=off:cond=fast:flr=on:lcm=predicate:nwc=1:nicw=on:sagn=off:sio=off:spl=sat:ssnc=none_300");
    break;

  case Property::FEQ: 
    fallback.push("dis-1010_2_bs=off:bsr=on:drc=off:nwc=4:ssac=none:sscc=on:ssfp=100000:ssfq=1.4:ssnc=all_300");
    fallback.push("ott+1011_5:1_bs=off:bsr=unit_only:cond=on:drc=off:nwc=2:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_300");
    fallback.push("lrs+1011_8_bd=off:bs=unit_only:bsr=on:drc=off:lcm=reverse:nwc=1:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_2700");
    fallback.push("ins+10_2:3_bs=unit_only:flr=on:fde=none:igbrr=0.7:igrr=1/32:igrp=200:igrpq=1.0:igwr=on:lcm=predicate:nwc=1.7:sd=2:ss=axioms:st=3.0:sos=all:sio=off:spl=off_300");
    fallback.push("lrs+10_20_bs=off:drc=off:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=2.0:ssnc=none_900");
    fallback.push("ott+11_1024_bd=off:bs=off:br=off:cond=fast:drc=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfq=1.2:ssnc=none:urr=on_300");
    fallback.push("lrs+1011_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1:nicw=on:sos=all:sio=off:spo=on:ssac=none:ssfp=1000:ssfq=1.1:ssnc=all_dependent_2400");
    fallback.push("dis+1_3_bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sd=1:ss=included:st=2.0:sagn=off:sio=off:spl=sat:sser=off:ssnc=none_300");
    fallback.push("dis+1010_12_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:ssnc=none:sfv=off_300");
    fallback.push("dis-1002_6_bs=off:cond=on:drc=off:fde=none:nwc=1.5:sd=1:ss=included:sos=on:sagn=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_300");
    fallback.push("dis+1011_12_bs=off:drc=off:nwc=5:nicw=on:sio=off:spl=sat:ssfq=1.2:ssnc=none_300");
    fallback.push("ott+1011_3:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.5:sd=3:ss=axioms:sos=all:sio=off:spl=off_300");
    fallback.push("ott+1_2_bs=off:drc=off:ep=on:nwc=3:nicw=on:sd=2:sgt=20:ss=axioms:sos=on:sagn=off:spl=sat:sser=off_300");
    fallback.push("dis+2_2:3_bs=off:drc=off:lcm=reverse:nwc=2.5:sos=all:sser=off:ssfp=10000:ssfq=2.0:ssnc=all_300");
    fallback.push("ins-1010_3:2_bs=unit_only:drc=off:ep=on:fde=none:igbrr=0.5:igrr=1/128:igrpq=1.3:igwr=on:nwc=1.7_300");
    fallback.push("tab+10_1_ep=RST:gsp=input_only:sd=4:ss=axioms:st=2.0:sio=off:tbsr=off:tgawr=1/32:tglr=1/5:tipr=off:tlawr=8/1_100");
    fallback.push("ins+3_10_bs=off:drc=off:fde=none:igbrr=0.8:igrr=1/128:igrp=100:igrpq=1.0:igwr=on:nwc=2.5:sio=off:spl=off_300");
    fallback.push("ott+2_12_bd=off:drc=off:lcm=reverse:nwc=2:sio=off:spo=on_600");
    fallback.push("ins+10_2:3_bs=off:cond=fast:ep=RSTC:igbrr=0.8:igrr=1/2:igrp=100:igrpq=1.0:igwr=on:nwc=2:sos=all:sio=off:urr=on_300");
    fallback.push("dis-1010_2:3_bs=off:drc=off:nwc=3:sd=2:ss=axioms:st=1.5:sac=on:sio=off_300");
    fallback.push("ott+1_2:3_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=1.3:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_300");
    fallback.push("dis-2_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=1.5:sd=3:sgt=10:ss=axioms:sos=on:spl=sat_300");
    fallback.push("ott+1011_8:1_bs=off:drc=off:fde=none:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off:sp=occurrence_300");
    fallback.push("ott+11_4:1_bs=off:cond=on:drc=off:flr=on:nwc=3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:sfv=off_300");
    fallback.push("dis-1002_1024_bs=off:cond=on:drc=off:nwc=3:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_300");
    fallback.push("dis+1_10_bs=off:cond=on:drc=off:lcm=predicate:nwc=2.5:sd=7:ss=axioms:st=1.5:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on_400");
    fallback.push("ott+1011_2_bs=off:drc=off:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:updr=off_300");
    fallback.push("dis+1_2:3_bs=off:drc=off:lcm=predicate:nwc=3:nicw=on:ss=included:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off:sp=occurrence_300");
    fallback.push("dis-4_4:1_bs=off:ep=RST:gsp=input_only:gs=on:nwc=5:sd=1:ss=included:st=5.0:sos=on:sio=off:sfv=off:sp=occurrence_300");
    fallback.push("ott-1010_64_bs=off:br=off:drc=off:flr=on:gs=on:nwc=1:sac=on:sio=off:urr=on_600");
    fallback.push("ott+10_2:3_bs=off:drc=off:gs=on:nwc=1.5:sd=2:ss=axioms:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:urr=on_300");
    fallback.push("lrs-1_10_bs=off:cond=fast:drc=off:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.4:ssnc=none_200");
    fallback.push("ott+1_3:1_bd=off:bs=off:bsr=unit_only:ep=on:nwc=10:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=sat_300");
    fallback.push("dis+1010_1_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:nwc=1.5:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none_500");
    fallback.push("dis+1011_10_bs=off:drc=off:nwc=1.3:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off_300");
    fallback.push("dis-1010_7_bs=off:cond=fast:drc=off:fde=none:nwc=1.1:nicw=on:sd=1:ss=axioms:st=3.0:sio=off:spl=sat_300");
    fallback.push("ott+11_2:1_bs=off:br=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:sd=2:ss=axioms:st=1.5:sos=all:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:urr=on_300");
    fallback.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=2.5:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_300");
    fallback.push("ott+4_32_bs=off:flr=on:nwc=4:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence_300");
    fallback.push("ott+1_5_bs=off:drc=off:nwc=4:sio=off:sp=occurrence_300");
    fallback.push("dis+10_8:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.1:nicw=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spl=sat:sp=reverse_arity_300");
    fallback.push("lrs+1_6_bs=off:drc=off:nwc=3:sos=all:sio=off:spl=sat:ssac=none:sscc=on:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_3600");
    fallback.push("dis-1002_16_bs=off:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sio=off:spl=sat:sser=off_300");
    fallback.push("dis+11_1024_bsr=unit_only:cond=fast:nwc=1.3:sio=off:spl=off_600");
    fallback.push("ott+2_3:1_bs=off:br=off:drc=off:nwc=1.1:nicw=on:sd=3:ss=axioms:st=3.0:sos=all:sio=off:spl=off:urr=on_300");
    fallback.push("ott-1002_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:nwc=1.1:sos=all:sio=off:spo=on:sp=occurrence_300");
    fallback.push("dis+10_8:1_bs=off:br=off:cond=on:drc=off:ep=RST:fsr=off:nwc=1.3:sd=4:ss=axioms:st=3.0:spl=sat:sser=off:ssfq=2.0:ssnc=none:urr=on_300");
    fallback.push("ott+1011_64_bs=off:cond=fast:drc=off:gsp=input_only:nwc=1:ss=axioms:st=1.2:spl=sat:sser=off:urr=on_300");
    fallback.push("dis+2_1_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=1:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sser=off_300");
    fallback.push("dis-10_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=4:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence_300");
    fallback.push("dis+1011_12_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.5:nicw=on:sio=off:spl=sat:ssfq=1.4:ssnc=none_300");
    fallback.push("ott-1002_5:1_bs=off:bsr=on:cond=fast:drc=off:gsp=input_only:nwc=2:sos=all:sio=off:spo=on:urr=on_300");
    fallback.push("dis+4_40_cond=on:drc=off:flr=on:lcm=predicate:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence_300");
    fallback.push("dis+11_3:1_bs=off:br=off:cond=on:drc=off:ep=on:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spl=sat:sser=off:urr=on_300");
    fallback.push("lrs-1010_7_bs=unit_only:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1.7:sgo=on:spo=on:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_300");
    fallback.push("ott+10_8:1_bd=off:bs=off:drc=off:fde=none:gsp=input_only:nwc=1:sd=3:ss=axioms:sos=on:sio=off:spl=off:urr=on_300");
    fallback.push("ott+10_3:1_bsr=unit_only:cond=fast:fsr=off:lcm=reverse:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:urr=on:updr=off_300");
    fallback.push("ins-1003_7_bs=off:ep=RSTC:flr=on:igbrr=0.0:igrr=1/128:igrp=1400:igrpq=1.1:igwr=on:nwc=1.3:sos=on:sio=off:spl=off_300");
    fallback.push("ott+11_24_bs=off:cond=fast:drc=off:fde=none:gs=on:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=1.4:ssnc=none:sp=reverse_arity_400");
    fallback.push("dis+2_4_bs=off:br=off:drc=off:nwc=1.2:sd=2:ss=axioms:st=2.0:sio=off:urr=on_300");
    fallback.push("dis+11_4_bs=off:drc=off:ep=on:gsp=input_only:nwc=5:sgt=15:ss=axioms:sos=on:spl=sat_300");
    fallback.push("ott-1010_4:1_bs=off:bsr=on:cond=on:drc=off:fde=none:gsp=input_only:nwc=2.5:sd=1:ss=axioms:sos=all:spl=sat:ssfq=1.0:ssnc=none_300");
    fallback.push("dis+11_10_bs=off:lcm=predicate:nwc=1.3:sio=off_300");
    fallback.push("dis+10_2_bs=off:cond=on:drc=off:fde=none:lcm=predicate:nwc=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sp=reverse_arity_300");
    fallback.push("dis+2_8:1_bd=off:bs=off:bsr=on:drc=off:lcm=reverse:nwc=4:nicw=on:sd=3:sgt=5:ss=axioms:st=1.5:sos=on:spl=sat:sser=off:sp=reverse_arity_300");
    fallback.push("ott+11_3:2_bs=off:cond=on:drc=off:ep=RSTC:gs=on:nwc=4:nicw=on:sd=2:sgt=10:ss=axioms:sagn=off:sio=off:spl=sat:urr=on_300");
    fallback.push("ott+1011_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=10:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_300");
    fallback.push("ott+10_1024_bs=off:cond=on:drc=off:gsp=input_only:nwc=1.2:sio=off:spl=sat:ssfp=10000:ssnc=none:updr=off_600");
    fallback.push("lrs+10_20_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none_800");
    fallback.push("ott-1010_3_bd=off:bs=off:bsr=unit_only:drc=off:fde=none:nwc=1:nicw=on:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity:updr=off_400");
    fallback.push("dis+1010_2:3_bs=off:bsr=unit_only:drc=off:ep=on:fsr=off:fde=none:lcm=predicate:nwc=1.5:sos=on:sac=on:sio=off:spo=on:sp=occurrence_600");
    fallback.push("dis+1_24_bs=off:drc=off:ep=on:lcm=predicate:nwc=3:nicw=on:ss=included:st=5.0:sos=on:sagn=off:spl=sat:sser=off:ssnc=none_300");
    fallback.push("dis-1_3_bsr=unit_only:drc=off:lcm=reverse:nwc=4:sos=all:sac=on:sgo=on:sio=off:spo=on:sp=reverse_arity_300");
    fallback.push("dis-1010_50_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_900");
    fallback.push("ott+10_8:1_bd=off:bs=off:cond=fast:drc=off:flr=on:nwc=1.3:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:urr=on_300");
    fallback.push("dis+4_2:1_bs=off:br=off:drc=off:fsr=off:nwc=1:sos=all:sio=off:spl=sat:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_200");
    fallback.push("ott+1011_5:4_bs=off:cond=fast:drc=off:flr=on:fsr=off:nwc=2:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_300");
    fallback.push("ott+11_1_bs=off:drc=off:ep=RS:flr=on:fde=none:nwc=4:sos=all:sgo=on:sio=off_300");
    fallback.push("dis+1010_32_cond=fast:drc=off:ep=RS:fsr=off:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_300");
    fallback.push("ott+1011_10_bs=off:cond=on:drc=off:nwc=1.5:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_200");
    fallback.push("lrs-1004_32_bs=off:br=off:cond=fast:drc=off:flr=on:gs=on:lcm=reverse:nwc=1:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none:urr=on_300");
    fallback.push("dis-1010_2_bd=off:bs=off:cond=fast:drc=off:nwc=5:nicw=on:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=sat:sser=off:sp=occurrence_300");
    fallback.push("ott+1_5:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=5:ss=axioms:sos=all_100");
    fallback.push("lrs-11_6_bs=off:bsr=unit_only:drc=off:gsp=input_only:lcm=predicate:nwc=10:sos=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on:updr=off_300");
    fallback.push("dis+1011_28_cond=on:drc=off:nwc=5:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:updr=off_100");
    fallback.push("ott+1011_8:1_bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none_300");
    fallback.push("ott+2_8:1_bs=off:bsr=on:drc=off:fde=none:lcm=reverse:nwc=1.2:nicw=on:sos=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_300");
    fallback.push("ott-3_10_bs=off:br=off:drc=off:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none:urr=on_300");
    fallback.push("dis+1003_1024_bs=off:drc=off:fsr=off:nwc=1.7:nicw=on:sos=on:sio=off:spl=sat:ssfq=2.0:ssnc=none_300");
    fallback.push("ott+4_40_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=5:nicw=on:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:spl=sat:sser=off:updr=off_300");
    fallback.push("dis+1011_4_bs=off:drc=off:nwc=4:sgo=on_100");
    fallback.push("dis+2_4_bs=off:drc=off:ep=RST:flr=on:lcm=reverse:nwc=1.5:sos=on:sio=off:spl=sat:ssfq=1.4:ssnc=none:sp=reverse_arity_300");
    fallback.push("ott+10_24_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sio=off:spl=sat:sser=off:ssnc=none_300");
    fallback.push("dis+1_128_bs=off:cond=fast:drc=off:gsp=input_only:lcm=predicate:nwc=10:sd=2:ss=included:st=2.0:sagn=off:sio=off:spl=sat:ssnc=none_300");
    fallback.push("ins+2_4:1_bs=off:cond=on:ep=RSTC:gs=on:igbrr=0.4:igrr=1/128:igrpq=1.05:igwr=on:nwc=5:sos=on:sio=off:urr=on_300");
    fallback.push("dis-1002_8:1_bs=off:cond=on:drc=off:flr=on:gs=on:nwc=4:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:urr=on_300");
    fallback.push("dis+11_28_bd=off:bs=off:cond=fast:drc=off:ep=on:fsr=off:lcm=reverse:nwc=5:sos=on:sio=off:spl=sat:ssfq=1.0:ssnc=none:sp=occurrence_300");
    fallback.push("dis+1011_1_bs=off:drc=off:nwc=1.2:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=2.0:ssnc=none_300");
    fallback.push("ott+11_2:1_bs=off:cond=fast:drc=off:ep=RS:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=2.5:sio=off:spl=sat:ssfq=1.1:ssnc=none:sp=occurrence_300");
    fallback.push("ott+2_20_cond=fast:drc=off:flr=on:lcm=reverse:nwc=1.1:nicw=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity:updr=off_300");
    fallback.push("lrs-1004_12_bs=off:bsr=unit_only:drc=off:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.4:ssnc=none_600");
    fallback.push("lrs-1002_3_bd=off:bs=off:drc=off:ep=on:nwc=1.7:sos=on:sac=on:sio=off_1500");
    fallback.push("dis+1010_40_bs=off:drc=off:ep=RS:nwc=1:sio=off:spo=on:spl=sat:ssnc=none_300");
    fallback.push("dis+1011_3_bs=off:cond=fast:drc=off:fsr=off:fde=none:gs=on:nwc=1.1:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.0:ssnc=none_300");
    fallback.push("lrs+1_5_bs=off:cond=fast:drc=off:flr=on:nwc=10:sac=on:sio=off:urr=on_300");
    fallback.push("dis+2_128_bs=off:drc=off:lcm=reverse:nwc=1.3:nicw=on:sos=on:sio=off:spl=sat:ssnc=none_300");
    fallback.push("dis+1_14_bd=off:bs=off:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=4:sos=on:sio=off:spo=on:sp=reverse_arity_200");
    fallback.push("dis+11_32_bs=off:nwc=1.1:sio=off:spl=off:updr=off_300");
    fallback.push("dis+2_20_drc=off:ep=RST:nwc=1.3:sio=off:spl=sat:ssfq=1.4:ssnc=none:sp=occurrence_300");
    fallback.push("dis+1011_2_bs=off:drc=off:nwc=1.1:sos=all:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:sfv=off:urr=on_300");
    fallback.push("ott+1010_5_bd=off:bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.1:ssnc=none_300");
    fallback.push("lrs+1_64_bs=off:drc=off:gsp=input_only:nwc=1.7:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none:updr=off_600");
    fallback.push("dis-1010_64_bs=off:drc=off:nwc=2.5:nicw=on:sgo=on:sio=off:spo=on:sser=off:ssfp=40000:ssfq=1.0:ssnc=none_300");
    fallback.push("lrs-1_5:1_bs=off:cond=fast:drc=off:nwc=4:sio=off:spl=sat:ssfp=4000:ssfq=2.0:ssnc=none_1200");
    fallback.push("dis-1010_3:1_bd=off:bs=off:cond=fast:gs=on:lcm=reverse:nwc=1.1:sac=on_900");
    fallback.push("ott+4_14_bs=unit_only:cond=fast:drc=off:nwc=1.2:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_600");
    fallback.push("dis+2_16_bs=off:drc=off:ep=on:gsp=input_only:lcm=reverse:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none_600");
    fallback.push("ott+11_10_bs=off:bsr=unit_only:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_1200");
    fallback.push("lrs-11_12_bs=off:drc=off:fde=none:gsp=input_only:gs=on:lcm=predicate:nwc=4:nicw=on:sos=all:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sfv=off:sp=occurrence:urr=on:updr=off_3000");
    fallback.push("ott+10_3:1_bd=off:drc=off:lcm=reverse:nwc=10:nicw=on:sio=off:spo=on:ssac=none:sscc=on:sser=off:ssfp=1000:ssfq=1.2:ssnc=all_900");
    fallback.push("ott+4_64_bd=off:bs=off:br=off:cond=on:drc=off:fsr=off:gs=on:nwc=1.7:sos=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.0:ssnc=none:urr=on_900");
    break;

  case Property::FNE:
    fallback.push("dis-1010_12_bs=off:bsr=unit_only:cond=on:gsp=input_only:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssnc=none:sp=occurrence:urr=on_300");
    fallback.push("dis+11_50_bs=off:cond=on:nwc=1.3:sos=all:sio=off:spl=sat:sser=off:ssnc=none:urr=on_300");
    fallback.push("dis+1011_3_bs=off:cond=fast:flr=on:gsp=input_only:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfq=1.1:ssnc=none_300");
    fallback.push("ott+1_7_bs=off:bsr=unit_only:fsr=off:gsp=input_only:nwc=1.5:spo=on_600");
    fallback.push("dis+11_50_bs=off:bsr=on:cond=on:lcm=reverse:nwc=1:sio=off:spl=sat:sser=off:ssnc=none:updr=off_300");
    fallback.push("ott+1011_50_bs=off:gs=on:nwc=2.5:nicw=on:sio=off:spl=sat:ssnc=none:urr=on:updr=off_300");
    fallback.push("dis+4_128_bs=off:cond=on:flr=on:nwc=1.2:sos=on:sac=on_300");
    fallback.push("dis+1004_10_bs=off:nwc=1.5:sagn=off:sio=off:spl=sat:ssnc=none_900");
    fallback.push("dis+4_10_bs=off:cond=fast:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1.2:sio=off:spl=sat:ssfp=1000:ssfq=1.0:ssnc=none:sp=occurrence:updr=off_300");
    fallback.push("tab+10_1_spl=off:tbsr=off:tfsr=off:tgawr=3/1:tglr=1/20:tipr=off:tlawr=8/1_300");
    fallback.push("ins+10_1_gsp=input_only:igbrr=0.9:igrp=100:igrpq=1.1:nwc=2_300");
    fallback.push("ott-1002_3_bs=unit_only:bsr=unit_only:cond=on:gsp=input_only:nwc=1.2:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=2.0:ssnc=none:urr=on_300");
    fallback.push("ott+1_40_bsr=unit_only:cond=fast:gs=on:nwc=1.5:sio=off:spl=sat:ssnc=none:urr=on_300");
    fallback.push("dis+3_6_flr=on:fsr=off:nwc=5:nicw=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2:ssnc=none:sp=occurrence_300");
    fallback.push("dis+1010_8_bs=off:nwc=1.1:sio=off_300");
    fallback.push("ott-1010_128_bs=off:cond=on:lcm=predicate:nwc=1.3:urr=on_600");
    fallback.push("ott+10_1024_bs=off:fsr=off:nwc=1.5:nicw=on:sio=off:spl=off_1200");
    fallback.push("lrs+1002_128_bs=off:cond=on:flr=on:lcm=reverse:nwc=1:spo=on_1200");
    break;

  case Property::UEQ:
    fallback.push("lrs+10_8_bs=off:cond=fast:drc=off:fsr=off:gsp=input_only:gs=on:nwc=2:urr=on_1200");
    fallback.push("lrs+10_14_drc=off:fde=none:nwc=2.5_1800");
    fallback.push("ott+10_50_bs=off:drc=off:fsr=off:fde=none:nwc=1_300");
    fallback.push("lrs+10_1024_nwc=4_1500");
    fallback.push("ott+10_8:1_bs=off:drc=off:fsr=off:nwc=1.7_600");
    fallback.push("ott+10_7_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.5_600");
    fallback.push("dis+4_5:1_bs=off:br=off:ep=RSTC:fsr=off:nwc=3:sos=all:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on_300");
    fallback.push("ott+2_10_bs=off:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:nwc=1.7:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfq=1.1:ssnc=none_200");
    fallback.push("lrs+10_20_bd=off:bs=unit_only:drc=off:fsr=off:nwc=1.2_900");
    fallback.push("dis+2_14_bs=off:br=off:ep=RSTC:flr=on:fsr=off:nwc=2.5:nicw=on:sos=all:sio=off:spl=sat:ssnc=none:urr=on_100");
    fallback.push("lrs+10_5:1_nwc=1_900");
    fallback.push("lrs+10_2:3_bs=unit_only:cond=on:drc=off:ep=on:fsr=off:gs=on:nwc=1:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:sp=occurrence_200");
    fallback.push("ott+10_20_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.3:sp=occurrence_600");
    fallback.push("ott+10_8:1_bs=off:bsr=on:nwc=4_300");
    fallback.push("ott+10_64_drc=off:nwc=1.1_400");
    fallback.push("ott+10_2:1_drc=off:nwc=5_1200");
    fallback.push("ott+10_20_bd=off:drc=off:nwc=2:sp=occurrence_600");
    fallback.push("ott+10_2:3_drc=off:nwc=2_600");
    fallback.push("ott+10_5_bd=off:drc=off:nwc=2.5_900");
    fallback.push("ott+10_2_fde=none:nwc=2.5:sp=reverse_arity_900");
    fallback.push("ott+10_8:1_nwc=3:sfv=off_900");
    break;
  }
}

unsigned CASCMode::getSliceTime(string sliceCode,string& chopped)
{
  CALL("CASCMode::getSliceTime");

  unsigned pos=sliceCode.find_last_of('_');
  string sliceTimeStr=sliceCode.substr(pos+1);
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
 * Get schedules for a problem of given property for satisfiability checking.
 * The schedules are to be executed from the toop of the stack,
 */
void CASCMode::getSchedulesSat(Property& property, Schedule& quick, Schedule& fallback)
{
  Property::Category cat = property.category();
  unsigned prop = property.props();
  unsigned atoms = property.atoms();

  switch (cat) {
  case Property::NEQ:
    quick.push("dis+10_5_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=5:nicw=on:sgo=on:sio=off:sp=occurrence_1");
    quick.push("dis+1_40_bs=off:ep=RSTC:nwc=1.1:sio=off:spl=sat:sser=off:ssnc=none:urr=on_39");
    quick.push("dis-1_24_bs=off:bfnt=on:lcm=predicate:nwc=10:sgo=on:sp=occurrence_21");
    quick.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=1.0:igrp=400:igrpq=1.5:nwc=5:sio=off_124");
    quick.push("dis+10_3:1_bs=off:bfnt=on:cond=on:lcm=predicate:nwc=1:nicw=on:sac=on:sio=off:spl=sat:sp=reverse_arity:urr=on:updr=off_196");
    quick.push("dis-1_128_bfnt=on:fsr=off:nwc=1.5:nicw=on:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=1.2:ssnc=all_207");
    quick.push("dis-11_10_bfnt=on:cond=fast:lcm=predicate:nwc=1.2:sio=off:spl=off:sp=occurrence_464");
    quick.push("dis+1_2:1_bs=off:bsr=on:cond=fast:ep=RSTC:gs=on:lcm=predicate:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence:urr=on_554");
    quick.push("ins-1004_5:1_bs=off:bfnt=on:cond=on:flr=on:igbrr=0.3:igrr=64/1:igrp=100:igrpq=1.2:igwr=on:nwc=1.3:sgo=on:sio=off_22");
    break;

  case Property::HEQ:
    quick.push("ins+4_12_bs=off:bfnt=on:cond=fast:gsp=input_only:igbrr=0.8:igrr=128/1:igrpq=2.0:nwc=1_23");
    quick.push("dis+3_1024_bfnt=on:cond=fast:fsr=off:nwc=5:sio=off:spl=off_55");
    quick.push("dis+10_2:3_bfnt=on:cond=on:fsr=off:lcm=predicate:nwc=1:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=1.4:sp=reverse_arity_40");
    quick.push("ott+11_16_bfnt=on:cond=fast:nwc=1.1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=1000:ssfq=2.0:sp=reverse_arity_850");
    quick.push("dis+2_1024_bd=off:bs=off:cond=fast:fsr=off:nwc=1:sio=off:spl=off_786");
    break;
    
  case Property::PEQ:
    if (prop == 0) {
      quick.push("dis+10_1024_bs=unit_only:cond=on:drc=off:nwc=1:sio=off:spl=sat:ssfq=1.0:ssnc=none_1");
      quick.push("ins+1_8:1_bs=off:bfnt=on:igbrr=0.8:igrr=2/1:igrpq=1.2:igwr=on:nwc=3:sos=all:sgo=on_3");
      quick.push("ins+10_1_bfnt=on:igbrr=0.8:igrp=400:igrpq=2.0:nwc=1.7:sio=off_1284");
    }
    else {
      quick.push("dis+4_12_bs=off:cond=fast:nwc=1.1:nicw=on:sio=off:spl=sat:ssnc=none_2");
      quick.push("lrs-1_128_bs=off:cond=fast:ep=on:nwc=1.2:nicw=on:stl=30:sac=on:sio=off_6");
      quick.push("dis-3_28_bd=off:cond=on:nwc=1.5:sio=off_340");
      quick.push("ins+1_8:1_bs=off:bfnt=on:igbrr=0.8:igrr=2/1:igrpq=1.2:igwr=on:nwc=3:sos=all:sgo=on_92");
      quick.push("dis+11_32_bd=off:bsr=on:fsr=off:nwc=1.2:nicw=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.4:ssnc=none_467");
      quick.push("dis+10_1024_bs=unit_only:cond=on:drc=off:nwc=1:sio=off:spl=sat:ssfq=1.0:ssnc=none_7");
    }
    break;

  case Property::HNE:
    quick.push("dis+10_4_bs=off:nwc=5:sac=on:sio=off_1");
    quick.push("ott+11_8_bs=off:bfnt=on:cond=fast:nwc=1:sio=off:spl=sat:sser=off:ssfp=100000:ssnc=none_1");
    quick.push("dis+11_24_bs=off:cond=fast:nwc=1.3:nicw=on:sac=on:sio=off_4");
    quick.push("dis-11_8:1_bs=off:nwc=2.5:sio=off:spl=off_23");
    break;

  case Property::NNE:
     quick.push("dis-11_40_bs=off:lcm=predicate:nwc=1.2:sio=off:spl=sat:ssac=none:ssfp=40000:ssfq=2.0:ssnc=none_1");
      quick.push("ott+11_1024_bs=off:cond=on:gsp=input_only:lcm=predicate:nwc=1.3:nicw=on:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none:sp=occurrence_1");
      quick.push("ins+11_12_bs=off:bfnt=on:gsp=input_only:igbrr=0.9:igrr=4/1:igrp=400:igrpq=2.0:nwc=4_144");
      quick.push("ott+1_20_bfnt=on:cond=on:nwc=3:sac=on:sgo=on:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.4_87");
      quick.push("ott+4_2:1_bs=off:cond=on:lcm=predicate:nwc=10:nicw=on:sac=on:sio=off_70");
      quick.push("dis-1_16_bs=off:bfnt=on:cond=on:lcm=predicate:nwc=1.2:nicw=on:ssfq=1.1:ssnc=none:sp=occurrence_47");
      quick.push("dis+1_28_bs=off:bfnt=on:cond=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1.7:sio=off:spl=off:sp=occurrence_152");
      quick.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=0.7:igrpq=2.0:nwc=4_238");
    break;

  case Property::FEQ:
    if (atoms >= 180) {
      quick.push("ott+11_8:1_bfnt=on:cond=on:fde=none:lcm=predicate:nwc=1.2:nicw=on:sio=off:spl=sat:sp=occurrence:urr=on:updr=off_1");
      quick.push("dis+11_32_bs=off:nwc=1.1:sio=off:spl=off:updr=off_2");
      quick.push("dis-2_2:1_bs=unit_only:bsr=unit_only:bfnt=on:lcm=predicate:nwc=5:sp=reverse_arity:updr=off_217");
      quick.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=0.9:igrp=1400:igrpq=1.5:nwc=1.2_547");
      quick.push("dis+1_40_bfnt=on:fsr=off:nwc=1.7:sio=off:spl=off:urr=on:updr=off_12");
      quick.push("dis+10_8:1_bs=off:nwc=4:sio=off:spl=off_48");
    }
    else if (atoms >= 160) {
      quick.push("dis+1_40_bfnt=on:fsr=off:nwc=1.7:sio=off:spl=off:urr=on:updr=off_357");
      quick.push("ott-3_2_bfnt=on:cond=fast:fde=none:nwc=5:sgo=on:updr=off_1581");
    }
    else if (atoms >= 130) {
      quick.push("ins+2_32_bs=off:bfnt=on:cond=fast:flr=on:gsp=input_only:igbrr=0.4:igrr=16/1:igrp=400:igrpq=1.3:igwr=on:nwc=1.2:sos=all_63");
      quick.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=0.5:igrp=1400:igrpq=1.5:nwc=1:updr=off_546");
      quick.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=0.8:igrp=2000:igrpq=2.0:nwc=1:sio=off_330");
    }
    else {
      quick.push("lrs-1002_3_bd=off:bs=off:drc=off:ep=on:nwc=1.7:stl=150:sos=on:sac=on:sio=off_1");
      quick.push("dis+11_10_bs=off:lcm=predicate:nwc=1.3:sio=off_3");
      quick.push("dis+10_8:1_bs=off:nwc=4:sio=off:spl=off_1");
      quick.push("ott+11_8:1_bfnt=on:cond=on:fde=none:lcm=predicate:nwc=1.2:nicw=on:sio=off:spl=sat:sp=occurrence:urr=on:updr=off_13");
      quick.push("dis-11_1024_bs=off:bfnt=on:cond=on:nwc=1:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0_7");
      quick.push("ins+10_1_bfnt=on:igbrr=0.4:igrpq=1.3:nwc=10:sio=off_39");
      quick.push("ins+1_5:4_bs=off:bfnt=on:cond=on:ep=RSTC:igbrr=0.5:igrr=128/1:igrp=200:igrpq=2.0:igwr=on:nwc=1.3:sos=on:sio=off_39");
      quick.push("ins+10_1_bfnt=on:igbrr=0.8:igrpq=2.0:nwc=2:sio=off_370");
      quick.push("ott+1_1024_bfnt=on:nwc=1.2:nicw=on:sgo=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.0_1173");
    }
    break;

  case Property::FNE:
    if (atoms > 10000) {
      quick.push("ins+11_3:1_bs=unit_only:br=off:gsp=input_only:igbrr=0.6:igrr=1/2:igrp=100:igrpq=2.0:igwr=on:nwc=1.5:sio=off:spl=off:urr=on_68");
      quick.push("ott+1_2:1_bs=off:fsr=off:nwc=4:nicw=on:spl=sat:ssfp=4000:ssfq=1.0:ssnc=all:updr=off_1349");
    }
    else if (atoms > 3000) {
      quick.push("dis-11_1024_bs=off:cond=fast:gsp=input_only:nwc=3:sio=off:spl=off_3");
      quick.push("ott+1_128_bs=off:bfnt=on:fsr=off:nwc=1:nicw=on:sac=on:sgo=on:sio=off:updr=off_10");
      quick.push("ins+11_3:1_bs=unit_only:br=off:gsp=input_only:igbrr=0.6:igrr=1/2:igrp=100:igrpq=2.0:igwr=on:nwc=1.5:sio=off:spl=off:urr=on_14");
      quick.push("dis+11_3:2_cond=fast:nwc=5:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none_9");
      quick.push("dis+2_4:1_bs=off:fsr=off:gsp=input_only:nwc=2:sio=off:spl=off_1779");
    }
    else if (atoms > 150) {
      quick.push("dis+11_3:2_cond=fast:nwc=5:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none_2");
      quick.push("ott+1_128_bs=unit_only:bfnt=on:cond=fast:fsr=off:lcm=predicate:nwc=1.2:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_55");
      quick.push("ott+4_8:1_bs=off:cond=on:lcm=predicate:nwc=1.7:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:sp=occurrence_3");
      quick.push("dis-11_1024_bs=off:cond=fast:gsp=input_only:nwc=3:sio=off:spl=off_11");
      quick.push("dis-11_2:3_bs=off:bfnt=on:cond=fast:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.1:ssnc=none:sp=occurrence_1");
      quick.push("ott-11_32_bs=off:cond=on:lcm=predicate:nwc=1.2:nicw=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.2:ssnc=none:sp=reverse_arity_1");
      quick.push("dis+2_1024_bs=off:cond=on:fsr=off:gsp=input_only:nwc=2:sio=off:spl=sat_73");
      quick.push("dis+11_28_bs=off:cond=fast:lcm=predicate:nwc=1.5:sac=on:sp=occurrence:urr=on_63");
      quick.push("ins+11_3:1_bs=unit_only:br=off:gsp=input_only:igbrr=0.6:igrr=1/2:igrp=100:igrpq=2.0:igwr=on:nwc=1.5:sio=off:spl=off:urr=on_1030");
      quick.push("ott+1_1024_bs=off:cond=fast:lcm=predicate:nwc=2.5:sac=on:sio=off:spo=on_251");
      quick.push("dis+2_4:1_bs=off:bfnt=on:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=10000:ssfq=1.0:ssnc=none:sp=occurrence_104");
    }
    else {
      quick.push("dis+11_28_bs=off:cond=fast:lcm=predicate:nwc=1.5:sac=on:sp=occurrence:urr=on_1");
      quick.push("ott+3_8:1_bs=off:cond=on:nwc=1.3:sio=off_1");
      quick.push("dis+1_8_bs=off:bfnt=on:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:sp=occurrence_1");
      quick.push("ott+1_7_bs=off:bsr=unit_only:fsr=off:gsp=input_only:nwc=1.5:spo=on_1");
      quick.push("ins+4_64_bs=off:bfnt=on:br=off:igbrr=0.6:igrr=1/128:igrp=200:igrpq=2.0:igwr=on:nwc=2:sos=all:urr=on:updr=off_182");
      quick.push("ins-3_64_bsr=on:br=off:cond=fast:flr=on:igbrr=0.6:igrr=4/1:igrp=4000:igrpq=2.0:igwr=on:nwc=2:sos=all:sgo=on:urr=on:updr=off_319");
      quick.push("ott+10_40_bs=off:fsr=off:nwc=10:sio=off:spo=on_86");
      quick.push("ins+1_5_bs=off:br=off:cond=on:igbrr=0.7:igrr=1/4:igrp=1400:igrpq=2.0:igwr=on:nwc=5:sos=all:urr=on_623");
      quick.push("ott+1_1024_bs=off:cond=fast:lcm=predicate:nwc=2.5:sac=on:sio=off:spo=on_1");
    }
    break;

  case Property::EPR:
    if (atoms > 2200) {
      quick.push("ott+2_20_bs=off:bsr=unit_only:nwc=5:nicw=on:sio=off:spl=sat:ssnc=none_119");
      quick.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_1935");
    }
    else {
      quick.push("dis-11_24_bs=off:cond=fast:drc=off:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:urr=on_1");
      quick.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_22");
      quick.push("dis+10_1024_bs=off:cond=fast:fsr=off:lcm=predicate:nwc=3:sio=off:spl=off:sp=occurrence:urr=on_171");
      quick.push("dis+1_40_bs=unit_only:bsr=unit_only:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none_560");
    }
    break;
 
  case Property::UEQ:
    quick.push("ott+11_20_bs=off:bfnt=on:cond=fast:fsr=off:lcm=predicate:nwc=2.5:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity_1");
    quick.push("dis+10_12_bs=off:bsr=unit_only:fsr=off:nwc=2_1");
    quick.push("ins+4_8_bs=off:bfnt=on:br=off:cond=fast:flr=on:fsr=off:igbrr=0.1:igrr=1/128:igrp=100:igrpq=2.0:igwr=on:nwc=1.3:sos=all:urr=on_1");
    quick.push("ins+3_2_bs=off:bfnt=on:br=off:cond=on:fsr=off:fde=none:igbrr=0.9:igrr=1/64:igrpq=2.0:igwr=on:nwc=10:sio=off:urr=on_900");
    break;
  }

  switch (cat) {
  case Property::NEQ:
  case Property::HEQ:
  case Property::PEQ:
  case Property::EPR:
  case Property::HNE: 
  case Property::NNE: 
  case Property::UEQ:
    fallback.push("ins+11_12_bs=off:bfnt=on:gsp=input_only:igbrr=0.9:igrr=4/1:igrp=400:igrpq=2.0:nwc=4_300");
    fallback.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_2100");
    fallback.push("dis+10_5_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=5:nicw=on:sgo=on:sio=off:sp=occurrence_100");
    fallback.push("ins+4_12_bs=off:bfnt=on:cond=fast:gsp=input_only:igbrr=0.8:igrr=128/1:igrpq=2.0:nwc=1_300");
    fallback.push("dis-3_28_bd=off:cond=on:nwc=1.5:sio=off_600");
    fallback.push("dis+1_40_bs=unit_only:bsr=unit_only:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none_900");
    fallback.push("ins+3_2_bs=off:bfnt=on:br=off:cond=on:fsr=off:fde=none:igbrr=0.9:igrr=1/64:igrpq=2.0:igwr=on:nwc=10:sio=off:urr=on_900");
    fallback.push("ott+11_8_bs=off:bfnt=on:cond=fast:nwc=1:sio=off:spl=sat:sser=off:ssfp=100000:ssnc=none_300");
    fallback.push("lrs-1_128_bs=off:cond=fast:ep=on:nwc=1.2:nicw=on:sac=on:sio=off_300");
    fallback.push("dis-11_10_bfnt=on:cond=fast:lcm=predicate:nwc=1.2:sio=off:spl=off:sp=occurrence_600");
    fallback.push("dis+1_1024_nwc=1.1:sio=off:spl=off:updr=off_400");
    fallback.push("ins+1_8:1_bs=off:bfnt=on:igbrr=0.8:igrr=2/1:igrpq=1.2:igwr=on:nwc=3:sos=all:sgo=on_300");
    fallback.push("ott+11_16_bfnt=on:cond=fast:nwc=1.1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=1000:ssfq=2.0:sp=reverse_arity_1200");
    fallback.push("ott+1_20_bfnt=on:cond=on:nwc=3:sac=on:sgo=on:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.4_300");
    fallback.push("dis+11_24_bs=off:cond=fast:nwc=1.3:nicw=on:sac=on:sio=off_300");
    fallback.push("dis+1_40_bs=off:ep=RSTC:nwc=1.1:sio=off:spl=sat:sser=off:ssnc=none:urr=on_300");
    fallback.push("dis-11_40_bs=off:lcm=predicate:nwc=1.2:sio=off:spl=sat:ssac=none:ssfp=40000:ssfq=2.0:ssnc=none_300");
    fallback.push("dis+10_12_bs=off:bsr=unit_only:fsr=off:nwc=2_300");
    fallback.push("ott+4_2:1_bs=off:cond=on:lcm=predicate:nwc=10:nicw=on:sac=on:sio=off_300");
    fallback.push("dis-11_8:1_bs=off:nwc=2.5:sio=off:spl=off_300");
    fallback.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=0.7:igrpq=2.0:nwc=4_500");
    fallback.push("dis+1_28_bs=off:bfnt=on:cond=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1.7:sio=off:spl=off:sp=occurrence_300");
    fallback.push("dis+10_3:1_bs=off:bfnt=on:cond=on:lcm=predicate:nwc=1:nicw=on:sac=on:sio=off:spl=sat:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=1.0:igrp=400:igrpq=1.5:nwc=5:sio=off_300");
    fallback.push("dis-1_16_bs=off:bfnt=on:cond=on:lcm=predicate:nwc=1.2:nicw=on:ssfq=1.1:ssnc=none:sp=occurrence_100");
    fallback.push("dis+2_1024_bd=off:bs=off:cond=fast:fsr=off:nwc=1:sio=off:spl=off_900");
    fallback.push("dis-11_1024_bs=off:bfnt=on:lcm=predicate:nwc=2.5:nicw=on:sio=off:spl=sat:sser=off:sp=occurrence:urr=on_300");
    fallback.push("dis+10_2:3_bfnt=on:cond=on:fsr=off:lcm=predicate:nwc=1:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=1.4:sp=reverse_arity_100");
    fallback.push("ins+4_8_bs=off:bfnt=on:br=off:cond=fast:flr=on:fsr=off:igbrr=0.1:igrr=1/128:igrp=100:igrpq=2.0:igwr=on:nwc=1.3:sos=all:urr=on_300");
    fallback.push("ott+11_20_bs=off:bfnt=on:cond=fast:fsr=off:lcm=predicate:nwc=2.5:nicw=on:sio=off:spl=sat:ssfp=1000:ssfq=1.1:ssnc=none:sp=reverse_arity_300");
    fallback.push("dis-1_128_bfnt=on:fsr=off:nwc=1.5:nicw=on:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=1.2:ssnc=all_500");
    fallback.push("dis+10_4_bs=off:nwc=5:sac=on:sio=off_200");
    fallback.push("ott+2_20_bs=off:bsr=unit_only:nwc=5:nicw=on:sio=off:spl=sat:ssnc=none_300");
    fallback.push("dis+3_1024_bfnt=on:cond=fast:fsr=off:nwc=5:sio=off:spl=off_100");
    fallback.push("dis+10_1024_bs=off:cond=fast:fsr=off:lcm=predicate:nwc=3:sio=off:spl=off:sp=occurrence:urr=on_300");
    fallback.push("dis+1_2:1_bs=off:bsr=on:cond=fast:ep=RSTC:gs=on:lcm=predicate:nwc=1.5:nicw=on:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence:urr=on_900");
    fallback.push("dis+11_32_bd=off:bsr=on:fsr=off:nwc=1.2:nicw=on:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.4:ssnc=none_600");
    fallback.push("ins+10_1_bfnt=on:igbrr=0.8:igrp=400:igrpq=2.0:nwc=1.7:sio=off_1500");
    break;

  case Property::FEQ: 
    fallback.push("dis+11_1024_bsr=unit_only:cond=fast:nwc=1.3:sio=off:spl=off_600");
    fallback.push("dis+1_40_bfnt=on:fsr=off:nwc=1.7:sio=off:spl=off:urr=on:updr=off_600");
    fallback.push("dis-2_2:1_bs=unit_only:bsr=unit_only:bfnt=on:lcm=predicate:nwc=5:sp=reverse_arity:updr=off_300");
    fallback.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=0.9:igrp=1400:igrpq=1.5:nwc=1.2_600");
    fallback.push("dis+10_8:1_bs=off:nwc=4:sio=off:spl=off_300");
    fallback.push("ott+11_10_bs=off:bsr=unit_only:cond=fast:drc=off:flr=on:nwc=1:nicw=on:sio=off:spo=on:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none:sp=reverse_arity:urr=on_1200");
    fallback.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=0.5:igrp=1400:igrpq=1.5:nwc=1:updr=off_600");
    fallback.push("ins+2_32_bs=off:bfnt=on:cond=fast:flr=on:gsp=input_only:igbrr=0.4:igrr=16/1:igrp=400:igrpq=1.3:igwr=on:nwc=1.2:sos=all_300");
    fallback.push("ott+11_8:1_bfnt=on:cond=on:fde=none:lcm=predicate:nwc=1.2:nicw=on:sio=off:spl=sat:sp=occurrence:urr=on:updr=off_300");
    fallback.push("ott+1_1024_bfnt=on:nwc=1.2:nicw=on:sgo=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.0_1200");
    fallback.push("ins+10_1_bfnt=on:igbrr=0.4:igrpq=1.3:nwc=10:sio=off_300");
    fallback.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=0.8:igrp=2000:igrpq=2.0:nwc=1:sio=off_600");
    fallback.push("ott-3_2_bfnt=on:cond=fast:fde=none:nwc=5:sgo=on:updr=off_1800");
    break;

  case Property::FNE:
    fallback.push("dis+11_3:2_cond=fast:nwc=5:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none_300");
    fallback.push("dis+1_50_bs=off:bfnt=on:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:sio=off:spl=sat:ssfp=100000:ssfq=2.0:ssnc=none:sp=occurrence_300");
    fallback.push("ins+10_1_bfnt=on:gsp=input_only:igbrr=0.3:igrp=700:igrpq=1.2:nwc=1.7_200");
    fallback.push("ins+11_3:1_bs=unit_only:br=off:gsp=input_only:igbrr=0.6:igrr=1/2:igrp=100:igrpq=2.0:igwr=on:nwc=1.5:sio=off:spl=off:urr=on_1200");
    fallback.push("dis+2_4:1_bs=off:fsr=off:gsp=input_only:nwc=2:sio=off:spl=off_2100");
    fallback.push("dis+11_28_bs=off:cond=fast:lcm=predicate:nwc=1.5:sac=on:sp=occurrence:urr=on_200");
    fallback.push("dis-11_2:3_bs=off:bfnt=on:cond=fast:lcm=predicate:nwc=4:sio=off:spl=sat:sser=off:ssfp=4000:ssfq=1.1:ssnc=none:sp=occurrence_300");
    fallback.push("ins+4_64_bs=off:bfnt=on:br=off:igbrr=0.6:igrr=1/128:igrp=200:igrpq=2.0:igwr=on:nwc=2:sos=all:urr=on:updr=off_300");
    fallback.push("ott+1_128_bs=unit_only:bfnt=on:cond=fast:fsr=off:lcm=predicate:nwc=1.2:nicw=on:sio=off:spl=sat:ssfq=2.0:ssnc=none:sp=occurrence_300");
    fallback.push("ott+1_2:1_bs=off:fsr=off:nwc=4:nicw=on:spl=sat:ssfp=4000:ssfq=1.0:ssnc=all:updr=off_1500");
    fallback.push("ott+10_40_bs=off:fsr=off:nwc=10:sio=off:spo=on_300");
    fallback.push("ott+1_7_bs=off:bsr=unit_only:fsr=off:gsp=input_only:nwc=1.5:spo=on_600");
    fallback.push("ott+4_8:1_bs=off:cond=on:lcm=predicate:nwc=1.7:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none:sp=occurrence_300");
    fallback.push("ott+3_8:1_bs=off:cond=on:nwc=1.3:sio=off_300");
    fallback.push("ott+1_128_bs=off:bfnt=on:fsr=off:nwc=1:nicw=on:sac=on:sgo=on:sio=off:updr=off_300");
    fallback.push("ins+1_5_bs=off:br=off:cond=on:igbrr=0.7:igrr=1/4:igrp=1400:igrpq=2.0:igwr=on:nwc=5:sos=all:urr=on_900");
    break;
  }
} // getSchedulesSat

/**
 * Get schedules for a problem of given property for EPR problems (both
 * satisfiability and unsatisfiability checking).
 * The schedules are to be executed from the toop of the stack,
 */
void CASCMode::getSchedulesEPR(Property& property, Schedule& quick, Schedule& fallback)
{
  unsigned prop = property.props();
  unsigned atoms = property.atoms();

  if (prop == 131072) {
    quick.push("ott+10_1024_bs=off:br=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.2:ssnc=none:urr=on_158");
    quick.push("dis+10_1024_bs=off:cond=fast:fsr=off:lcm=predicate:nwc=3:sio=off:spl=off:sp=occurrence:urr=on_162");
  }
  else if (atoms > 2000) {
    quick.push("ott+2_20_bs=off:bsr=unit_only:nwc=5:nicw=on:sio=off:spl=sat:ssnc=none_119");
    quick.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_1935");
  }
  else if (atoms > 1300) {
    quick.push("dis-11_24_bs=off:cond=fast:drc=off:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.1:ssnc=none:urr=on_1");
    quick.push("ott+10_1024_bs=off:br=off:ep=RSTC:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=1.2:ssnc=none:urr=on_148");
    quick.push("dis+10_1024_bs=off:cond=fast:fsr=off:lcm=predicate:nwc=3:sio=off:spl=off:sp=occurrence:urr=on_171");
    quick.push("ins+3_128_bs=off:br=off:drc=off:igbrr=0.1:igrr=32/1:igrp=2000:igrpq=2.0:igwr=on:nwc=3:sos=all:sio=off:urr=on_262");
    quick.push("ins+2_128_bs=unit_only:drc=off:fsr=off:igbrr=1.0:igrr=128/1:igrp=200:igrpq=2.0:igwr=on:lcm=predicate:nwc=2:sos=on:sio=off:sp=occurrence_277");
    quick.push("dis+1_40_bs=unit_only:bsr=unit_only:nwc=1:sio=off:spl=sat:ssfp=10000:ssfq=2.0:ssnc=none_560");
  }
  else if (atoms > 450) {
    quick.push("dis-10_5:4_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=1.1:sac=on:sio=off:spo=on_5");
    quick.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_22");
    quick.push("ins+11_50_bs=off:cond=fast:drc=off:flr=on:gsp=input_only:igbrr=0.7:igrr=1/8:igrp=2000:igrpq=1.5:igwr=on:nwc=1.2:urr=on_56");
    quick.push("ins+3_50_bs=off:br=off:drc=off:igbrr=0.7:igrr=1/128:igrp=100:igrpq=1.05:igwr=on:lcm=predicate:nwc=2:sp=occurrence:urr=on_501");
    quick.push("ins+10_1_igbrr=0.4:igrp=200:igrpq=1.5:nwc=1.1:sio=off_561");
  }
  else {
    quick.push("ins+11_50_bs=off:cond=fast:drc=off:flr=on:gsp=input_only:igbrr=0.7:igrr=1/8:igrp=2000:igrpq=1.5:igwr=on:nwc=1.2:urr=on_12");
    quick.push("ins+10_1_bs=unit_only:br=off:cond=on:drc=off:gsp=input_only:igbrr=0.7:igrr=1/4:igrp=400:igrpq=1.5:igwr=on:nwc=1.2:sio=off:urr=on:updr=off_13");
    quick.push("ins+3_14_bs=off:cond=on:drc=off:flr=on:igbrr=0.2:igrr=1/128:igrp=200:igrpq=1.2:igwr=on:nwc=1:urr=on_43");
    quick.push("ott+1_128_bs=off:cond=fast:nwc=2.5:nicw=on:sio=off:spl=sat:ssnc=none:urr=on_1");
    quick.push("dis+4_10_bs=off:drc=off:fsr=off:nwc=5:nicw=on:sio=off:spl=sat:ssfp=40000:ssfq=1.0:ssnc=none_482");
    quick.push("ins-10_14_bs=off:drc=off:fde=none:igbrr=0.9:igrr=1/4:igrp=2000:igrpq=2.0:igwr=on:nwc=1.5:sos=on:sgo=on:sio=off:updr=off_1506");
  }
} // getSchedulesEPR

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
bool CASCMode::runSchedule(Schedule& schedule,unsigned ds,StrategySet& ss,bool fallback)
{
  CALL("CASCMode::runSchedule");

  Schedule::BottomFirstIterator sit(schedule);
  while (sit.hasNext()) {
    string sliceCode = sit.next();
    string chopped;
    unsigned sliceTime = getSliceTime(sliceCode,chopped);
    if (fallback && ss.contains(chopped)) {
      continue;
    }
    ss.insert(chopped);
    int remainingTime = env -> remainingTime()/100;
    if (remainingTime<=0) {
      return false;
    }
    // cast to unsigned is OK since realTimeRemaining is positive
    if (sliceTime > (unsigned)remainingTime) {
      sliceTime = remainingTime;
    }
    env -> beginOutput();
    env -> out()<<"% remaining time: "<<remainingTime<<" next slice time: "<<sliceTime<<endl;
    env -> endOutput();
    if (runSlice(sliceCode,sliceTime)) {
      return true;
    }
  }
  return false;
} // runSchedule

bool CASCMode::runSlice(string slice, unsigned ds)
{
  CALL("CASCMode::runSlice");

  Options opt=*env -> options;
  opt.readFromTestId(slice);
  opt.setTimeLimitInDeciseconds(ds);
  int stl = opt.simulatedTimeLimit();
  if (stl) {
    opt.setSimulatedTimeLimit(int(stl * SLOWNESS));
  }
  return runSlice(opt);
}
