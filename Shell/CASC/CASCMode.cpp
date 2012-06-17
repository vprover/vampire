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

#include "ForkingCM.hpp"
#include "SpawningCM.hpp"

#include "CASCMode.hpp"

#define SLOWNESS 1.1

namespace Shell
{
namespace CASC
{

using namespace Lib;

bool CASCMode::_sat = false;
bool CASCMode::_epr = false;

bool CASCMode::perform(int argc, char* argv [])
{
  CALL("CASCMode::perform/2");

  UIHelper::cascMode=true;

  env.timer->makeChildrenIncluded();

#if COMPILER_MSVC
  SpawningCM cm(argv[0]);
#else
  ForkingCM cm;
#endif

  bool res=cm.perform();

  env.beginOutput();
  if(res) {
    env.out()<<"% Success in time "<<Timer::msToSecondsString(env.timer->elapsedMilliseconds())<<endl;
  }
  else {
    env.out()<<"% Proof not found in time "<<Timer::msToSecondsString(env.timer->elapsedMilliseconds())<<endl;
    if(env.remainingTime()/100>0) {
      env.out()<<"% SZS status GaveUp for "<<env.options->problemName()<<endl;
    }
    else {
      //From time to time we may also be terminating in the timeLimitReached()
      //function in Lib/Timer.cpp in case the time runs out. We, however, output
      //the same string there as well.
      env.out()<<"% SZS status Timeout for "<<env.options->problemName()<<endl;
    }
  }
  if(env.options && env.options->timeStatistics()) {
    TimeCounter::printReport(env.out());
  }
  env.endOutput();

  return res;
}

void CASCMode::handleSIGINT()
{
  CALL("CASCMode::handleSIGINT");

  env.beginOutput();
  env.out()<<"% Terminated by SIGINT!"<<endl;
  env.out()<<"% SZS status User for "<<env.options->problemName() <<endl;
  env.statistics->print(env.out());
  env.endOutput();
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

  int remainingTime=env.remainingTime()/100;
  if(remainingTime<=0) {
    return false;
  }
  StrategySet used;
  if (runSchedule(quick,remainingTime,used,false)) {
    return true;
  }
  remainingTime=env.remainingTime()/100;
  if(remainingTime<=0) {
    return false;
  }
  return runSchedule(fallback,remainingTime,used,true);
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
    if (prop == 131075) {
      quick.push("dis+2_64_bs=off:cond=fast:drc=off:fsr=off:lcm=reverse:nwc=4:ptb=off:sos=on:spl=sat:sser=off:ssfp=100000:ssfq=1.4:ssnc=none_4");
      quick.push("dis+10_14_bs=off:cond=fast:drc=off:gs=on:nwc=2.5:nicw=on:sd=1:ss=axioms:st=3.0:sac=on:spo=on:sp=occurrence_4");
      quick.push("dis+1011_24_cond=fast:drc=off:nwc=10:nicw=on:ptb=off:ssec=off:spl=sat_14");
      quick.push("dis-1010_5_bs=off:bsr=unit_only:cond=fast:ep=on:gsp=input_only:lcm=reverse:nwc=1:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=backtracking:sp=occurrence_54");
      quick.push("dis+1011_28_bs=off:cond=fast:drc=off:gs=on:nwc=1.1:ptb=off:ssec=off:spl=sat_8");
      quick.push("dis-1002_2:1_bs=off:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:nicw=on:ptb=off:ssec=off:sos=all:sp=occurrence_16");
      quick.push("dis+4_128_bs=off:drc=off:fde=none:nwc=1:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking:sp=reverse_arity_1");
      quick.push("dis+1011_7_bs=off:drc=off:ep=RS:fde=none:gsp=input_only:nwc=10:ptb=off:ssec=off:spl=sat:sser=off:ssfp=40000:ssfq=1.2:ssnc=none_6");
      quick.push("ott+10_50_bs=off:br=off:cond=fast:drc=off:flr=on:gs=on:nwc=4:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:ssfq=2.0:ssnc=all:sp=reverse_arity:urr=on_2");
      quick.push("dis+11_4_ep=on:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:sos=on:spo=on:spl=sat_42");
      quick.push("ins-11_24_bs=off:cond=fast:ep=RSTC:flr=on:gsp=input_only:gs=on:igbrr=0.7:igrr=1/4:igrpq=1.3:igwr=on:lcm=reverse:nwc=2.5:ptb=off:ssec=off:sio=off:spl=off:urr=on_3");
      quick.push("dis+11_24_bs=off:cond=on:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.7:ptb=off:ssec=off:spl=sat:sp=reverse_arity_26");
      quick.push("ott+2_40_bsr=unit_only:drc=off:fsr=off:fde=none:nwc=1:nicw=on:ptb=off:ssec=off:sio=off:urr=on_46");
      quick.push("dis+1011_128_bs=unit_only:cond=fast:lcm=reverse:nwc=3:ptb=off:ssec=off:sos=on:spl=sat:sfv=off_244");
      quick.push("dis+11_5:1_bs=off:drc=off:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sos=all:sgo=on:sio=off:spo=on:spl=sat:sp=occurrence_213");
      quick.push("dis-1010_3:2_bs=off:bsr=unit_only:drc=off:ep=RST:fde=none:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sos=on:sgo=on:spo=on:spl=backtracking:sp=reverse_arity_262");
      quick.push("ott+1011_6_bs=off:drc=off:ep=on:fde=none:nwc=1.1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat_4");
    }
    else if (prop == 3) {
      if (atoms < 2500) {
	quick.push("dis+10_14_bs=off:cond=fast:drc=off:gs=on:nwc=2.5:nicw=on:sd=1:ss=axioms:st=3.0:sac=on:spo=on:sp=occurrence_3");
	quick.push("ott-11_8:1_bd=off:bs=off:drc=off:ep=on:fde=none:lcm=predicate:nwc=3:ptb=off:ssec=off:sos=on:sio=off:urr=on_29");
	quick.push("dis-1002_5:4_bs=off:drc=off:ep=RST:flr=on:fde=none:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sgo=on:spo=on:spl=sat:sp=reverse_arity:updr=off_4");
	quick.push("ott+10_2:3_bd=off:bs=off:cond=fast:drc=off:fde=none:lcm=predicate:nwc=10:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking:sp=occurrence_2");
	quick.push("dis+11_3:1_bs=off:drc=off:ep=on:nwc=10:ptb=off:ssec=off:spl=sat:urr=on_8");
	quick.push("ins-10_40_bs=off:cond=fast:ep=RSTC:flr=on:gsp=input_only:gs=on:igbrr=0.7:igrr=1/4:igrp=4000:igrpq=1.2:igwr=on:lcm=reverse:nwc=1.7:ptb=off:ssec=off:sio=off:spl=off:urr=on_30");
	quick.push("dis+11_5_bs=off:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking:sp=occurrence_14");
	quick.push("dis+1011_4:1_bs=off:bsr=on:drc=off:ep=on:flr=on:gsp=input_only:gs=on:lcm=reverse:nwc=2:ptb=off:ssec=off:sos=all:spo=on:spl=sat:ssfp=10000:ssnc=none:sp=occurrence_5");
	quick.push("ott+1011_5_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=2:ptb=off:ssec=off:sos=on:sio=off:sp=reverse_arity:updr=off_7");
	quick.push("ott+1011_2:3_bd=off:bs=off:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_61");
	quick.push("ins-11_24_bs=off:cond=fast:ep=RSTC:flr=on:gsp=input_only:gs=on:igbrr=0.7:igrr=1/4:igrpq=1.3:igwr=on:lcm=reverse:nwc=2.5:ptb=off:ssec=off:sio=off:spl=off:urr=on_7");
	quick.push("dis+1011_64_bs=off:drc=off:ep=on:flr=on:nwc=2:ptb=off:ssec=off:spl=sat:sp=occurrence_48");
	quick.push("ott+1011_3_bs=off:drc=off:ep=on:fde=none:nwc=1.1:nicw=on:ptb=off:ssec=off:spl=sat_58");
	quick.push("dis+1011_28_bs=off:cond=fast:drc=off:gs=on:nwc=1.1:ptb=off:ssec=off:spl=sat_40");
	quick.push("dis+11_40_bs=off:bms=on:drc=off:fde=none:gs=on:lcm=predicate:nwc=1.3:sd=4:ss=axioms:sac=on:spo=on:sp=occurrence_1");
	quick.push("dis+1010_4:1_bs=off:bms=on:drc=off:ep=RST:nwc=4:sswn=on:sos=on:sgo=on:spo=on_1");
	quick.push("dis+1011_128_bs=unit_only:cond=fast:lcm=reverse:nwc=3:ptb=off:ssec=off:sos=on:spl=sat:sfv=off_56");
	quick.push("ott+10_2_bd=off:bs=off:drc=off:ecs=on:flr=on:fsr=off:nwc=1.7:ssec=off:sac=on:sgo=on:sio=off_95");
	quick.push("dis+1011_2_bs=off:drc=off:ep=on:flr=on:nwc=1.1:nicw=on:ptb=off:ssec=off:spl=sat:urr=on:updr=off_154");
	quick.push("dis+1011_2_bs=off:cond=on:drc=off:ep=on:gsp=input_only:nwc=1.5:nicw=on:ptb=off:ssec=off:spl=sat:urr=on_152");
	quick.push("dis+11_8:1_bs=off:br=off:drc=off:ep=RST:nwc=1:ptb=off:ssec=off:sgo=on:sio=off:spo=on:spl=backtracking:urr=on_160");
	quick.push("ott+2_3_bd=off:cond=on:drc=off:flr=on:nwc=1.3:ptb=off:ssec=off:sac=on:sgo=on:sio=off:sfv=off:sp=reverse_arity:updr=off_216");
	quick.push("dis-1010_3:2_bs=off:bsr=unit_only:drc=off:ep=RST:fde=none:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sos=on:sgo=on:spo=on:spl=backtracking:sp=reverse_arity_28");
	quick.push("dis-1010_3:1_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.7:nicw=on:ptb=off:spl=sat:sser=off:ssfp=100000:ssfq=1.1:ssnc=none_39");
	quick.push("ott+10_4:1_bd=off:bs=off:bsr=unit_only:drc=off:gsp=input_only:nwc=4:ptb=off:ssec=off:sos=all:sio=off:spo=on:urr=on:updr=off_40");
	quick.push("ott+1_1_bd=off:bs=off:bsr=unit_only:br=off:cond=on:drc=off:ep=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sd=4:ss=axioms:st=2.0:sio=off:urr=on_77");
      }
      else {
	quick.push("ott-1010_3_bd=off:bs=off:cond=on:drc=off:ep=on:fde=none:nwc=10:ptb=off:ssec=off:sd=3:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sp=reverse_arity:urr=on_11");
	quick.push("dis-1010_3_cond=fast:drc=off:nwc=4:sac=on_19");
	quick.push("ott+1011_5_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=2:ptb=off:ssec=off:sos=on:sio=off:sp=reverse_arity:updr=off_13");
	quick.push("dis+11_5:1_bs=off:drc=off:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sos=all:sgo=on:sio=off:spo=on:spl=sat:sp=occurrence_29");
	quick.push("dis+4_8:1_bs=off:bsr=on:drc=off:fsr=off:fde=none:lcm=reverse:nwc=10:ptb=off:ssec=off:spl=sat:ssfp=10000:ssfq=1.0:ssnc=none:sp=reverse_arity_16");
	quick.push("dis+11_12_bs=off:drc=off:ep=on:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=3:nicw=on:ptb=off:ssec=off:sos=on:spl=sat_1");
	quick.push("ott+11_3_bs=off:br=off:drc=off:nwc=1.1:nicw=on:ss=axioms:sos=on:sio=off:urr=on_2");
	quick.push("ott+1011_3_bs=off:drc=off:ep=on:fde=none:nwc=1.1:nicw=on:ptb=off:ssec=off:spl=sat_86");
	quick.push("ins-1010_8:1_bs=off:ep=RSTC:fsr=off:igbrr=1.0:igrr=1/128:igrp=200:igrpq=2.0:igwr=on:nwc=1.2:ptb=off:ssec=off:sos=on:sio=off:spl=off_86");
	quick.push("dis+10_14_bs=off:cond=fast:drc=off:gs=on:nwc=2.5:nicw=on:sd=1:ss=axioms:st=3.0:sac=on:spo=on:sp=occurrence_115");
	quick.push("ott+1_10_bd=off:bs=off:drc=off:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sos=on:spl=sat_113");
	quick.push("ott+11_2_bd=off:bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=10:ptb=off:ssec=off:spl=sat:sp=reverse_arity_246");
	quick.push("dis+1_8:1_bs=off:cond=on:drc=off:ep=RST:flr=on:fsr=off:gsp=input_only:lcm=reverse:nwc=3:ptb=off:ssec=off:sio=off:urr=on_259");
	quick.push("lrs+2_3:1_bs=off:br=off:drc=off:flr=on:lcm=predicate:nwc=10:ssec=off:stl=60:sgo=on:sio=off:spo=on:sp=occurrence:urr=on_260");
	quick.push("dis+2_4:1_bs=off:cond=on:drc=off:ecs=on:ep=on:gs=on:lcm=reverse:nwc=1.5:ssec=off:sos=on:sio=off:ssfp=1000:ssfq=1.1:ssnc=none:urr=on_43");
      }
    }
    else if (prop == 131079) {
      quick.push("dis+11_5:1_bs=off:drc=off:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sos=all:sgo=on:sio=off:spo=on:spl=sat:sp=occurrence_1");
      quick.push("dis+11_5:4_bs=off:bsr=on:cond=on:drc=off:fde=none:lcm=reverse:nwc=1.3:nicw=on:ptb=off:ssec=off:spl=sat:sscc=on:sser=off:ssfp=40000:ssfq=1.0_8");
      quick.push("dis+11_50_bs=off:cond=fast:drc=off:fde=none:gs=on:lcm=predicate:nwc=2:nicw=on:ssec=off:spo=on:sp=reverse_arity_1");
      quick.push("dis+11_5:1_bs=off:cond=fast:drc=off:nwc=10:sswn=on:sswsr=on_5");
      quick.push("ott+11_5_bs=off:ep=on:fde=none:nwc=1.5:nicw=on:ptb=off:ssec=off:sswsr=on:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_79");
      quick.push("dis+11_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sgo=on:sio=off:sp=occurrence_18");
      quick.push("dis+1011_28_bs=off:cond=fast:drc=off:gs=on:nwc=1.1:ptb=off:ssec=off:spl=sat_11");
      quick.push("ott+1011_6_drc=off:ep=on:fde=none:gs=on:nwc=1.3:nicw=on:ptb=off:ssec=off:sswsr=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off_5");
      quick.push("ott+2_8:1_bd=off:bs=off:bsr=unit_only:bms=on:br=off:cond=fast:drc=off:nwc=1.5:ssec=off:sos=on:sio=off:urr=on:updr=off_7");
      quick.push("ott+1011_3_bs=off:bsr=unit_only:ep=on:nwc=2:ptb=off:ssec=off:spl=sat_27");
      quick.push("dis+1011_16_bd=off:bs=off:cond=on:drc=off:ep=on:fsr=off:gs=on:nwc=2.5:ptb=off:ssec=off:sgo=on:spo=on:spl=backtracking_5");
      quick.push("dis+1011_12_bs=off:drc=off:fsr=off:nwc=5:nicw=on:ptb=off:ssec=off:sos=on:spl=sat_28");
      quick.push("ott+11_2_bd=off:bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=10:ptb=off:ssec=off:spl=sat:sp=reverse_arity_185");
      quick.push("dis+1011_24_cond=fast:drc=off:nwc=10:nicw=on:ptb=off:ssec=off:spl=sat_129");
      quick.push("ott+10_4:1_bd=off:bs=off:bsr=unit_only:drc=off:gsp=input_only:nwc=4:ptb=off:ssec=off:sos=all:sio=off:spo=on:urr=on:updr=off_91");
      quick.push("ott+11_2:3_bd=off:bs=unit_only:bsr=unit_only:cond=on:drc=off:fde=none:lcm=reverse:nwc=1.2:ptb=off:ssec=off:spl=sat_94");
      quick.push("ott+3_8:1_bd=off:bs=off:bsr=unit_only:drc=off:fsr=off:nwc=1.2:nicw=on:ptb=off:ssec=off:sos=all:spl=sat:sser=off:ssfp=10000:ssfq=1.4:ssnc=none_149");
      quick.push("ott+11_8:1_drc=off:ep=on:nwc=1:ptb=off:ssec=off:sac=on:spo=on:sp=occurrence_471");
      quick.push("dis+1011_4:1_bs=off:bsr=on:drc=off:ep=on:flr=on:gsp=input_only:gs=on:lcm=reverse:nwc=2:ptb=off:ssec=off:sos=all:spo=on:spl=sat:ssfp=10000:ssnc=none:sp=occurrence_1");
    }
    else if (prop == 1) {
      quick.push("ott+10_2:3_bd=off:bs=off:cond=fast:drc=off:fde=none:lcm=predicate:nwc=10:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking:sp=occurrence_1");
      quick.push("dis+10_6_bs=off:br=off:cond=on:drc=off:ep=RSTC:gs=on:nwc=1.1:nicw=on:ptb=off:ssec=off:sos=all:sio=off:spl=sat:urr=on_2");
      quick.push("dis+1011_16_bd=off:bs=off:cond=on:drc=off:ep=on:fsr=off:gs=on:nwc=2.5:ptb=off:ssec=off:sgo=on:spo=on:spl=backtracking_24");
      quick.push("ott+11_2_bd=off:bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=10:ptb=off:ssec=off:spl=sat:sp=reverse_arity_6");
      quick.push("ins+1_8:1_bs=off:cond=on:ep=RSTC:flr=on:gs=on:igbrr=0.8:igrr=1/4:igrp=1400:igrpq=1.05:igwr=on:nwc=2.5:ptb=off:ssec=off:sio=off:spl=off:urr=on_3");
      quick.push("ins+1011_3_bs=off:ep=RSTC:fde=none:gs=on:igbrr=1.0:igrr=1/64:igrp=100:igrpq=1.3:igwr=on:nwc=2.5:ptb=off:ssec=off:sos=on:sio=off:spl=off_2");
      quick.push("ott-11_40_bd=off:bs=off:drc=off:ecs=on:flr=on:fsr=off:lcm=predicate:nwc=1.5:nicw=on:ssec=off:sos=on_42");
      quick.push("dis+11_3_bs=off:bms=on:cond=fast:drc=off:gsp=input_only:lcm=reverse:nwc=3:ssec=off:sos=on:sac=on:spo=on:sp=occurrence_2");
      quick.push("lrs+10_20_bd=off:bs=off:cond=fast:drc=off:ecs=on:nwc=1.5:ptb=off:ssec=off:stl=30:sio=off:spo=on:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:updr=off_18");
      quick.push("ott-11_2:3_bd=off:bs=off:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:spl=sat:sp=reverse_arity_14");
      quick.push("dis+11_8:1_bs=off:br=off:drc=off:ep=RST:nwc=1:ptb=off:ssec=off:sgo=on:sio=off:spo=on:spl=backtracking:urr=on_29");
      quick.push("dis+11_5:1_bs=off:drc=off:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sos=all:sgo=on:sio=off:spo=on:spl=sat:sp=occurrence_123");
      quick.push("ott+10_28_bd=off:bs=off:drc=off:nwc=1.5:ptb=off:ssec=off:spl=sat_21");
      quick.push("dis+11_50_bs=off:drc=off:gsp=input_only:nwc=1.3:nicw=on:ptb=off:ssec=off:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none_35");
      quick.push("ott+11_50_bd=off:bs=off:drc=off:ep=on:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat:sp=occurrence_53");
      quick.push("dis-1010_7_bs=off:cond=fast:drc=off:fsr=off:gsp=input_only:gs=on:nwc=1.1:ptb=off:ssec=off:sio=off:spo=on:urr=on_21");
      quick.push("dis+10_1024_bs=off:cond=on:drc=off:flr=on:fsr=off:lcm=predicate:nwc=1.2:nicw=on:ptb=off:ssec=off:sac=on:spo=on_110");
      quick.push("dis+1011_40_bs=off:cond=on:drc=off:fsr=off:nwc=1.2:nicw=on:ptb=off:ssec=off:sos=on:sagn=off:sgo=on:sio=off:spl=sat:sser=off:ssfp=4000:ssnc=none_51");
      quick.push("lrs-1002_4:1_bs=off:gs=on:nwc=4:nicw=on:ssec=off:stl=60:sgo=on:spo=on:urr=on_96");
      quick.push("ott-1010_8:1_bd=off:nwc=1.2:nicw=on:ptb=off:ssec=off:sos=on:spl=sat:ssfp=4000:ssfq=1.4:ssnc=none:urr=on_19");
      quick.push("lrs+1011_20_bd=off:bs=off:ecs=on:ep=on:fde=none:lcm=predicate:nwc=3:nicw=on:ssec=off:stl=60:sio=off:spl=off:urr=on_214");
      quick.push("dis+11_12_bs=off:drc=off:ep=on:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=3:nicw=on:ptb=off:ssec=off:sos=on:spl=sat_142");
      quick.push("lrs+3_64_bs=off:drc=off:fsr=off:gsp=input_only:nwc=5:nicw=on:stl=60:sac=on:sgo=on_307");
      quick.push("ott+10_64_bd=off:bs=off:cond=fast:drc=off:flr=on:gsp=input_only:lcm=predicate:nwc=2:nicw=on:ptb=off:ssec=off:sac=on:spo=on_220");
      quick.push("dis+11_5_bs=off:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking:sp=occurrence_1");
      quick.push("ott+3_8:1_bd=off:bs=off:bsr=unit_only:drc=off:fsr=off:nwc=1.2:nicw=on:ptb=off:ssec=off:sos=all:spl=sat:sser=off:ssfp=10000:ssfq=1.4:ssnc=none_6");
      quick.push("lrs+2_3:1_bs=off:br=off:drc=off:flr=on:lcm=predicate:nwc=10:ssec=off:stl=60:sgo=on:sio=off:spo=on:sp=occurrence:urr=on_15");
      quick.push("ott+10_2_bd=off:bs=off:drc=off:ecs=on:flr=on:fsr=off:nwc=1.7:ssec=off:sac=on:sgo=on:sio=off_68");
      quick.push("ott+11_2:3_bd=off:bs=unit_only:bsr=unit_only:cond=on:drc=off:fde=none:lcm=reverse:nwc=1.2:ptb=off:ssec=off:spl=sat_106");
    }
    else {
      quick.push("ott+1011_6_bs=off:drc=off:ep=on:fde=none:nwc=1.1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat_4");
      quick.push("ott+10_2:3_bd=off:bs=off:cond=fast:drc=off:fde=none:lcm=predicate:nwc=10:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking:sp=occurrence_3");
      quick.push("dis-1002_5:4_bs=off:drc=off:ep=RST:flr=on:fde=none:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sgo=on:spo=on:spl=sat:sp=reverse_arity:updr=off_10");
      quick.push("dis+11_5_bs=off:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking:sp=occurrence_2");
      quick.push("dis+11_3_bs=off:bms=on:cond=fast:drc=off:gsp=input_only:lcm=reverse:nwc=3:ssec=off:sos=on:sac=on:spo=on:sp=occurrence_1");
      quick.push("ott+10_50_bs=off:br=off:cond=fast:drc=off:flr=on:gs=on:nwc=4:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:ssfq=2.0:ssnc=all:sp=reverse_arity:urr=on_5");
      quick.push("dis-2_50_bs=off:drc=off:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sio=off:spl=backtracking:sp=occurrence_6");
      quick.push("dis+11_24_bs=off:bms=on:cond=on:drc=off:ecs=on:fde=none:nwc=2.5:nicw=on:ssec=off:spo=on:sp=occurrence:urr=on_1");
      quick.push("ott+1011_3_bs=off:drc=off:ep=on:fde=none:nwc=1.1:nicw=on:ptb=off:ssec=off:spl=sat_11");
      quick.push("dis-1010_3:2_bs=off:bsr=unit_only:drc=off:ep=RST:fde=none:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sos=on:sgo=on:spo=on:spl=backtracking:sp=reverse_arity_22");
      quick.push("ott+10_4:1_bd=off:bs=off:bsr=unit_only:drc=off:gsp=input_only:nwc=4:ptb=off:ssec=off:sos=all:sio=off:spo=on:urr=on:updr=off_3");
      quick.push("dis+10_5_bd=off:bs=off:cond=fast:ep=RST:gsp=input_only:lcm=predicate:nwc=5:ptb=off:ssec=off:sos=all:sac=on:sio=off:spl=backtracking:sfv=off:urr=on_10");
      quick.push("ott-1002_2:1_bd=off:bs=off:bsr=on:drc=off:ep=on:flr=on:fsr=off:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:urr=on_51");
      quick.push("ins+1011_3_bs=off:ep=RSTC:fde=none:gs=on:igbrr=1.0:igrr=1/64:igrp=100:igrpq=1.3:igwr=on:nwc=2.5:ptb=off:ssec=off:sos=on:sio=off:spl=off_66");
    }
    break;

  case Property::HEQ:
    if (prop == 2) {
      quick.push("dis+1_2:1_bs=off:cond=on:drc=off:nwc=5:sos=on:sio=off:spo=on:sp=occurrence_2");
      quick.push("ott+1_3_bs=off:cond=on:drc=off:fde=none:nwc=3:ptb=off:ssec=off:sos=all:sio=off:spl=sat_60");
      quick.push("ott+11_64_bs=off:drc=off:ecs=on:gs=on:nwc=1.5:ssec=off:sio=off:spl=off_746");
      quick.push("ins+11_50_bs=off:drc=off:fde=none:igbrr=0.7:igrr=1/32:igrp=700:igrpq=1.2:igwr=on:nwc=3:ptb=off:sio=off:spl=off:sp=reverse_arity_1045");
    }
    else if (prop == 0) {
      quick.push("dis+2_8_bd=off:bs=off:ep=RST:fsr=off:lcm=reverse:nwc=3:nicw=on:ptb=off:ssec=off:spo=on:spl=backtracking:sfv=off_2");
      quick.push("lrs+11_1_bd=off:bs=off:cond=on:drc=off:gs=on:nwc=2:ptb=off:stl=30:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none_259");
      quick.push("lrs-1_2:1_bs=off:drc=off:gs=on:nwc=1.1:nicw=on:ssec=off:stl=50:sio=off:spl=off:updr=off_175");
      quick.push("ott+11_50_bs=off:cond=on:drc=off:flr=on:fde=none:lcm=predicate:nwc=2:nicw=on:ptb=off:sgo=on:sio=off:spl=backtracking:sp=occurrence:urr=on_1127");
    }
    else {
      quick.push("dis-1010_3_bs=off:drc=off:lcm=predicate:nwc=10:ptb=off:ssec=off:spo=on_2");
      quick.push("ott+11_50_bs=off:cond=on:drc=off:flr=on:fde=none:lcm=predicate:nwc=2:nicw=on:ptb=off:sgo=on:sio=off:spl=backtracking:sp=occurrence:urr=on_67");
      quick.push("dis+2_128_bs=off:drc=off:lcm=predicate:nwc=10:sac=on:sio=off:sp=occurrence_199");
      quick.push("ott+11_40_bd=off:bs=off:cond=on:drc=off:nwc=3:nicw=on:ptb=off:ssec=off:spl=sat:sp=reverse_arity_2");
      quick.push("lrs+11_1_bd=off:bs=off:cond=on:drc=off:gs=on:nwc=2:ptb=off:stl=30:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none_66");
      quick.push("lrs+11_4:1_bs=unit_only:cond=fast:drc=off:fde=none:lcm=predicate:nwc=10:nicw=on:ptb=off:stl=60:sac=on:spo=on:spl=sat:ssac=none:ssfp=1000:ssfq=1.0:ssnc=all_191");
      quick.push("lrs+2_14_bs=off:cond=fast:drc=off:nwc=10:ptb=off:stl=90:sac=on:sio=off:spo=on:spl=sat:ssac=none:ssfp=100000:ssfq=1.1:ssnc=all_dependent:sp=reverse_arity_679");
      quick.push("ott+10_64_bs=off:cond=on:drc=off:ecs=on:flr=on:gsp=input_only:nwc=5:nicw=on:ssec=off:spo=on:sp=reverse_arity:updr=off_367");
      quick.push("dis+11_7_bs=off:drc=off:lcm=reverse:nwc=5:ssec=off:sio=off:spl=off:updr=off_116");
    }
    break;
    
  case Property::PEQ:
    if (prop == 0) {
      if (atoms > 15) {
	quick.push("dis+11_8_bsr=unit_only:cond=on:drc=off:fsr=off:gs=on:nwc=1.1:nicw=on:ptb=off:ssec=off:sos=all:sio=off:spo=on:spl=sat:sser=off:ssfq=1.4:ssnc=none_87");
	quick.push("ott+1_3_bs=off:bms=on:cond=on:drc=off:nwc=2:sac=on:sio=off:updr=off_635");
	quick.push("ott+10_8:1_drc=off:ecs=on:ep=RSTC:gs=on:nwc=1.3:ssec=off:sac=on:sio=off_31");
	quick.push("dis+10_5:4_cond=on:gs=on:nwc=2:nicw=on:ptb=off:sos=all:sio=off:spl=sat:sscc=on:sser=off:ssfp=1000:ssfq=1.1:ssnc=none:sfv=off:sp=occurrence_324");
	quick.push("dis+4_50_bd=off:bs=unit_only:cond=on:drc=off:gs=on:lcm=predicate:nwc=5:nicw=on:ptb=off:sos=all:sio=off:spl=backtracking:urr=on_379");
	quick.push("dis+1_6_bd=off:flr=on:gs=on:nwc=1.5:ptb=off:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity_330");
	quick.push("dis+2_6_bd=off:drc=off:flr=on:fsr=off:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_419");
      }
      else {
	quick.push("lrs+1_40_bs=unit_only:cond=on:drc=off:ecs=on:nwc=1:nicw=on:ptb=off:ssec=off:stl=30:sio=off:spo=on:spl=sat:ssfq=1.0:ssnc=none_140");
	quick.push("lrs-3_4_bsr=unit_only:cond=on:drc=off:fsr=off:fde=none:gs=on:nwc=1.2:ssec=off:stl=150:sgo=on:sio=off:urr=on:updr=off_492");
	quick.push("dis+10_10_bs=off:cond=fast:drc=off:fsr=off:nwc=1.2:nicw=on:ptb=off:sio=off:spo=on:spl=sat:sser=off:ssnc=none_434");
      }
    }
    else if (prop == 1) {
      quick.push("dis+1_12_bs=off:drc=off:ep=on:nwc=1.3:nicw=on:sos=on:sio=off:spl=off_1");
      quick.push("ott+4_5_bd=off:bsr=unit_only:cond=fast:drc=off:fsr=off:gs=on:nwc=1.5:nicw=on:sac=on:sio=off_2");
      quick.push("dis+1_6_bd=off:flr=on:gs=on:nwc=1.5:ptb=off:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity_21");
      quick.push("ott+3_128_bs=off:br=off:cond=fast:drc=off:ep=on:nwc=1:nicw=on:ptb=off:sos=all:sio=off:spo=on:spl=backtracking:urr=on_108");
      quick.push("lrs-3_4_bsr=unit_only:cond=on:drc=off:fsr=off:fde=none:gs=on:nwc=1.2:ssec=off:stl=150:sgo=on:sio=off:urr=on:updr=off_1255");
      quick.push("dis+1_2_bd=off:bs=off:drc=off:flr=on:fsr=off:nwc=10:ptb=off:ssec=off:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_253");
      quick.push("dis+4_50_bd=off:bs=unit_only:cond=on:drc=off:gs=on:lcm=predicate:nwc=5:nicw=on:ptb=off:sos=all:sio=off:spl=backtracking:urr=on_142");
    }
    else if (prop == 2) {
      quick.push("ott+4_6_bs=off:bsr=on:cond=on:drc=off:fsr=off:nwc=3:ssec=off:sswn=on:sac=on:sio=off:sp=occurrence_120");
      quick.push("ott+3_20_bs=off:cond=fast:drc=off:fde=none:nwc=2:ptb=off:ssec=off:sgo=on:sio=off:spo=on:spl=sat:sp=occurrence_157");
      quick.push("ott+4_28_bs=off:cond=on:drc=off:fde=none:gs=on:nwc=1.1:ptb=off:ssec=off:sgo=on:sio=off:spo=on:spl=sat_164");
      quick.push("ott+2_1024_bs=off:drc=off:gsp=input_only:nwc=1.1:ptb=off:ssec=off:spl=sat:ssfq=1.4:ssnc=none:sp=occurrence_371");
    }
    else {
      quick.push("dis-1004_1024_bs=off:cond=fast:drc=off:ep=on:nwc=1.2_96");
      quick.push("lrs+11_2:3_bd=off:drc=off:flr=on:nwc=1.3:nicw=on:ptb=off:stl=90:sio=off:spl=sat:ssnc=none_106");
      quick.push("ins+4_3_cond=fast:flr=on:igbrr=0.6:igrr=1/128:igrp=700:igrpq=1.2:igwr=on:nwc=1.7:ptb=off:sio=off:spl=off:updr=off_116");
      quick.push("lrs-3_4_bsr=unit_only:cond=on:drc=off:fsr=off:fde=none:gs=on:nwc=1.2:ssec=off:stl=150:sgo=on:sio=off:urr=on:updr=off_1133");
    }
    break;

  case Property::HNE:
    if (prop == 8192) {
      if (atoms > 6) {
	quick.push("dis+11_1_bs=off:cond=fast:fsr=off:nwc=10:ptb=off:ssec=off:sio=off:spo=on:spl=sat_56");
	quick.push("ott+4_6_bs=off:bsr=unit_only:cond=fast:nwc=1.2:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat_281");
	quick.push("dis+4_14_fsr=off:lcm=reverse:nwc=1:sac=on:sio=off_34");
	quick.push("lrs+10_3:1_bs=off:bsr=unit_only:cond=fast:nwc=10:ptb=off:ssec=off:stl=90:sio=off:spo=on_144");
	quick.push("ott+1011_10_bs=off:cond=on:nwc=3:ptb=off:ssec=off:sio=off:spl=backtracking_62");
	quick.push("lrs-1003_28_bs=unit_only:bms=on:cond=on:flr=on:fsr=off:gsp=input_only:nwc=1:nicw=on:ssec=off:stl=60:sio=off:spl=off:sp=occurrence_180");
	quick.push("dis+2_5:4_cond=fast:ecs=on:flr=on:nwc=1.5:ssec=off:sio=off:spl=off_576");
	quick.push("dis+1002_50_bs=off:fsr=off:lcm=predicate:nwc=1.2:nicw=on:ssec=off_392");
	quick.push("lrs+2_5:1_bs=off:cond=fast:flr=on:fsr=off:lcm=predicate:nwc=10:ptb=off:ssec=off:stl=90:spl=backtracking_588");
	quick.push("dis-1004_4_bs=off:bms=on:cond=on:nwc=2:sio=off_52");
      }
      else {
	quick.push("lrs+3_8_bs=unit_only:cond=fast:flr=on:nwc=4:nicw=on:ptb=off:ssec=off:stl=30:sio=off:spl=backtracking_124");
	quick.push("dis+11_64_bs=unit_only:bms=on:lcm=reverse:nwc=1.5:sio=off_33");
	quick.push("lrs+1011_64_bs=unit_only:bsr=unit_only:cond=fast:flr=on:nwc=1:ptb=off:stl=180:sio=off:spo=on:spl=backtracking_658");
	quick.push("lrs+1_1024_bs=off:bms=on:cond=on:ecs=on:nwc=1:nicw=on:ssec=off:stl=90:sac=on:sio=off_761");
      }
    }
    else {
      quick.push("ott+1011_10_bs=off:cond=on:nwc=3:ptb=off:ssec=off:sio=off:spl=backtracking_3");
      quick.push("dis+2_128_bs=off:bms=on:cond=on:ecs=on:gs=on:lcm=reverse:nwc=1.7:ssec=off:sos=on:sio=off_1");
      quick.push("dis+1010_10_bs=off:cond=fast:gs=on:nwc=1.5:ptb=off:ssec=off:sio=off_9");
      quick.push("dis+1_50_bs=off:cond=on:nwc=3:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_142");
      quick.push("lrs+10_4:1_bs=off:cond=on:flr=on:nwc=10:ssec=off:stl=50:sio=off:spl=off:sp=reverse_arity_63");
      quick.push("dis+1011_20_bs=off:fsr=off:nwc=2:sio=off:spl=off_201");
      quick.push("ott+1_8:1_bs=off:br=off:cond=on:gs=on:nwc=3:ptb=off:ssec=off:sio=off:spl=sat:urr=on_227");
      quick.push("lrs+10_3:1_bs=off:bsr=unit_only:cond=fast:nwc=10:ptb=off:ssec=off:stl=90:sio=off:spo=on_4");
    }
    break;

  case Property::NNE:
    if (prop == 32768) {
      quick.push("dis+3_50_bs=off:fsr=off:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sos=on:spl=sat:updr=off_29");
      quick.push("dis+1011_128_bs=off:nwc=5:ptb=off:ssec=off:sswsr=on:sos=on:spl=sat_148");
      quick.push("lrs+4_1024_bs=off:flr=on:fsr=off:gs=on:lcm=reverse:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=30:sos=on:sio=off:spo=on:spl=backtracking_240");
      quick.push("dis+1011_12_bs=off:cond=fast:ecs=on:flr=on:nwc=1:ssec=off_170");
      quick.push("dis+1011_128_bs=off:cond=fast:flr=on:fsr=off:lcm=reverse:nwc=2.5:nicw=on:ptb=off:ssec=off:sswsr=on:spl=sat_215");
      quick.push("ott-1002_2_bs=off:ecs=on:flr=on:lcm=predicate:nwc=2:nicw=on:ssec=off:sos=on:spo=on:sp=reverse_arity:updr=off_173");
      quick.push("dis+11_128_bs=off:cond=fast:flr=on:lcm=reverse:nwc=2:ptb=off:ssec=off:spl=sat_190");
    }
    else {
      quick.push("dis+1011_4_bs=off:gs=on:nwc=1.7:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:spl=backtracking_1");
      quick.push("dis+1_2:1_bs=off:bsr=unit_only:fsr=off:lcm=reverse:nwc=1.1:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:sser=off:ssfq=2.0_14");
      quick.push("dis-2_14_bs=off:cond=fast:flr=on:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spl=backtracking_39");
      quick.push("ott+1010_2_bs=off:gs=on:nwc=5:ptb=off:ssec=off:spl=sat_26");
      quick.push("dis+11_20_bs=off:fsr=off:gsp=input_only:lcm=reverse:nwc=1.3:ptb=off:ssec=off:spl=sat:sp=occurrence_13");
      quick.push("dis+1011_20_bs=off:gsp=input_only:nwc=1.3:nicw=on:ptb=off:ssec=off:sswsr=on:sos=on:sac=on:sio=off:spo=on:spl=sat_184");
      quick.push("dis+11_10_bs=off:flr=on:lcm=reverse:nwc=2.5:ptb=off:ssec=off:spl=sat_29");
      quick.push("lrs+1002_7_bs=off:cond=on:flr=on:fsr=off:gsp=input_only:gs=on:lcm=predicate:nwc=1.2:ptb=off:stl=30:spl=sat:sser=off:ssfp=40000:ssfq=2.0:ssnc=none_62");
      quick.push("dis+1_40_bs=off:cond=on:gsp=input_only:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:sgo=on:sio=off:spl=sat_114");
      quick.push("dis+1011_6_bs=off:nwc=1.2:ptb=off:ssec=off:spl=sat_179");
      quick.push("dis+4_12_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=10:ptb=off:ssec=off:spl=sat:sp=occurrence_184");
    }
    break;

  case Property::FEQ:
    if (prop == 1) {
      if (atoms > 2000000) {
	quick.push("dis+2_24_bs=off:ep=RSTC:flr=on:lcm=reverse:nwc=5:nicw=on:ssec=off:sac=on:sgo=on:spo=on:sfv=off_1179");
      }
      else {
	quick.push("ott+11_64_bd=off:bs=off:br=off:cond=fast:drc=off:ep=on:gsp=input_only:gs=on:nwc=2:ptb=off:ssec=off:sos=all:sio=off:spl=backtracking:urr=on_3");
	quick.push("dis-11_20_bs=off:cond=on:drc=off:ep=RS:nwc=1.7:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:ssfq=2.0:ssnc=none_1");
	quick.push("dis+2_24_bs=off:cond=on:drc=off:fde=none:nwc=1.1:nicw=on:sd=10:ss=axioms:sio=off:spl=off:sp=reverse_arity_8");
	quick.push("ott+1_10_bs=off:cond=fast:drc=off:flr=on:lcm=predicate:nwc=10:ptb=off:ssec=off:sac=on:sio=off:spo=on:sp=occurrence:urr=on_7");
	quick.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=5:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_1");
	quick.push("ott+11_12_cond=fast:drc=off:ecs=on:gs=on:nwc=1.2:nicw=on:ssec=off:sp=occurrence_1");
	quick.push("dis+2_24_bs=off:ep=RSTC:flr=on:lcm=reverse:nwc=5:nicw=on:ssec=off:sac=on:sgo=on:spo=on:sfv=off_197");
	quick.push("ott+1011_6_bs=unit_only:drc=off:ep=RST:nwc=10:ssec=off:sac=on:sgo=on:sio=off:spo=on_11");
	quick.push("dis+1011_1_bs=off:bsr=on:cond=fast:drc=off:flr=on:fde=none:gs=on:nwc=1.5:ptb=off:ssec=off:sos=on:sac=on:sio=off:urr=on_29");
	quick.push("dis+1_3:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=1.5:sos=on:sagn=off:sac=on:sio=off:spl=backtracking:sp=occurrence_46");
	quick.push("ott+1011_1_bs=off:cond=on:drc=off:ecs=on:nwc=2:nicw=on:ptb=off:ssec=off:spl=sat:ssfp=1000:ssfq=1.2:ssnc=none_10");
	quick.push("dis+1010_24_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=2.5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_111");
	quick.push("dis-1010_2_bs=off:cond=fast:drc=off:nwc=1.7:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=backtracking:updr=off_240");
	quick.push("ott+11_2:3_bs=off:cond=on:drc=off:flr=on:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:spo=on:spl=sat:sp=reverse_arity:urr=on_196");
	quick.push("ott+1_5:1_bs=off:cond=fast:drc=off:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:sos=on:spl=sat:sp=occurrence_306");
	quick.push("dis+1011_3_bd=off:bs=off:drc=off:ep=on:fde=none:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_8");
	quick.push("dis+2_4_bs=off:drc=off:ep=RST:flr=on:lcm=reverse:nwc=1.7:ptb=off:ssec=off:sos=on:spl=sat:sp=reverse_arity_12");
      }
    }
    else if (prop == 2) {
      if (atoms > 19) {
	quick.push("lrs+2_40_bs=off:cond=fast:drc=off:nwc=1.7:ptb=off:ssec=off:stl=30:sio=off:spo=on:spl=sat_35");
	quick.push("ott+2_5:1_bd=off:bs=off:drc=off:gsp=input_only:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:sos=on:spl=sat:urr=on_1");
	quick.push("lrs+10_8_bs=off:drc=off:gs=on:nwc=1.5:nicw=on:ptb=off:ssec=off:stl=60:sio=off:spo=on:spl=sat:updr=off_22");
	quick.push("dis+1011_3_bd=off:bs=off:drc=off:ep=on:fde=none:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_55");
	quick.push("lrs+11_50_bs=off:bms=on:cond=fast:drc=off:ecs=on:nwc=1.1:ssec=off:stl=90:urr=on_627");
	quick.push("ott+11_12_cond=fast:drc=off:ecs=on:gs=on:nwc=1.2:nicw=on:ssec=off:sp=occurrence_372");
	quick.push("ott+10_1024_bs=off:drc=off:nwc=1.7:ssec=off:sac=on:sio=off:sp=occurrence:updr=off_395");
	quick.push("lrs-1004_50_bs=off:br=off:cond=fast:drc=off:nwc=1.5:nicw=on:stl=60:sio=off:spl=off:urr=on:updr=off_273");
	quick.push("dis+11_3:1_bs=off:drc=off:ep=on:nwc=2.5:ptb=off:ssec=off:sos=all:sio=off:spl=sat:sp=reverse_arity_32");
      }
      else {
	quick.push("dis-1002_3_bs=off:cond=on:drc=off:gs=on:nwc=3:nicw=on:ssec=off:sgo=on:sio=off:sp=reverse_arity_34");
	quick.push("lrs+11_50_bs=off:bms=on:cond=fast:drc=off:ecs=on:nwc=1.1:ssec=off:stl=90:urr=on_6");
	quick.push("ott+2_6_bs=off:cond=fast:drc=off:fde=none:nwc=1.2:ptb=off:ssec=off:sio=off:spl=sat_112");
	quick.push("ott+3_28_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sac=on:sio=off_243");
	quick.push("ott-11_8:1_bd=off:bs=off:drc=off:lcm=reverse:nwc=3:sio=off:spl=off:urr=on_72");
	quick.push("ott+1_8_bs=off:drc=off:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_55");
	quick.push("ott+1_50_bd=off:bs=unit_only:drc=off:nwc=1.1:nicw=on:ptb=off:sio=off:spl=sat:ssfp=10000:ssfq=1.0:ssnc=all_dependent:sp=reverse_arity_299");
	quick.push("lrs+3_24_bd=off:cond=on:drc=off:nwc=1.3:ptb=off:ssec=off:stl=30:sio=off:spl=sat:sp=occurrence_217");
	quick.push("ott+11_12_cond=fast:drc=off:ecs=on:gs=on:nwc=1.2:nicw=on:ssec=off:sp=occurrence_435");
	quick.push("ott+3_24_bs=unit_only:drc=off:ecs=on:fde=none:nwc=1.1:ssec=off:sos=all:sac=on_425");
      }
    }
    else if (prop == 131087) {
      if (atoms > 240000) {
	quick.push("ott+2_5:1_bd=off:bs=off:drc=off:gsp=input_only:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:sos=on:spl=sat:urr=on_44");
	quick.push("ott+1_4_bs=off:cond=on:drc=off:ep=on:flr=on:nwc=4:nicw=on:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:sos=on:sagn=off:spl=sat_41");
	quick.push("ott+1011_8:1_bs=off:bsr=unit_only:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_176");
	quick.push("dis+1_4:1_bs=off:drc=off:ep=on:fde=none:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:spl=sat:sp=reverse_arity:updr=off_31");
	quick.push("dis-1010_14_bs=off:ep=RST:nwc=1.1:ptb=off:sd=1:ss=included:st=1.5:sos=on:sac=on:sio=off:spl=sat:ssfq=1.0:ssnc=none:sfv=off_35");
	quick.push("dis+1011_3_bs=off:drc=off:fde=none:gs=on:nwc=1.1:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sio=off:spl=sat_46");
	quick.push("dis-3_5:1_bs=off:drc=off:ecs=on:ep=on:fde=none:gsp=input_only:nwc=1.3:ssec=off:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sac=on:sio=off:sp=occurrence_38");
	quick.push("ott+3_32_bd=off:bs=off:drc=off:flr=on:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:spl=sat:updr=off_31");
	quick.push("dis-2_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=3:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence:updr=off_106");
	quick.push("dis+2_5:1_bd=off:bs=off:ep=RSTC:gs=on:lcm=reverse:nwc=1.2:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:sac=on:sio=off:sfv=off:sp=reverse_arity_39");
	quick.push("dis-1002_12_bs=off:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sswsr=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sio=off:spl=sat_46");
	quick.push("dis+2_8:1_bs=off:drc=off:flr=on:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:spl=sat_44");
	quick.push("ott+1_8:1_bs=off:drc=off:ep=on:flr=on:gsp=input_only:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spl=backtracking_51");
	quick.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=5:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_132");
	quick.push("ott+1_2_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=4:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_135");
	quick.push("dis+3_2_bs=off:drc=off:ep=RST:fsr=off:nwc=1:ptb=off:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:spl=sat:ssfq=2.0:ssnc=none:sfv=off_75");
	quick.push("ott+4_5:1_bd=off:bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=3:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:urr=on_217");
	quick.push("dis-1002_5_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:spl=sat:ssfq=1.4:ssnc=none:updr=off_47");
	quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=backtracking_49");
      }
      else if (atoms > 140000) {
	quick.push("dis+1_3:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=1.5:sos=on:sagn=off:sac=on:sio=off:spl=backtracking:sp=occurrence_45");
	quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=backtracking_46");
	quick.push("ott+4_3:1_bs=off:bms=on:br=off:drc=off:fde=none:nwc=1.7:nicw=on:sd=3:ss=axioms:st=3.0:sos=all:sio=off:spl=off:sfv=off:urr=on_21");
	quick.push("ott-11_4:1_bs=off:bsr=on:cond=fast:drc=off:ecs=on:nwc=1.3:ssec=off:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sio=off_29");
	quick.push("ott-1010_4_bs=off:cond=fast:drc=off:fsr=off:gs=on:nwc=10:nicw=on:ptb=off:ssec=off:sd=4:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spl=backtracking:sfv=off_19");
	quick.push("dis-1_1_bs=off:ep=RSTC:gs=on:nwc=1.1:sd=1:ss=included:st=5.0:sos=on:sio=off:sfv=off_22");
	quick.push("dis+11_2:1_bs=off:ep=on:nwc=1:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:spl=sat_35");
	quick.push("dis-1010_5:4_bs=off:bms=on:drc=off:nwc=10:sd=2:ss=axioms:st=1.5:sac=on:sio=off:updr=off_20");
	quick.push("ott+1011_8:1_bs=off:bsr=unit_only:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_39");
	quick.push("dis+1011_2_bs=off:cond=on:drc=off:gs=on:nwc=4:ptb=off:ssec=off:sd=1:ss=axioms:st=1.2:spl=sat:updr=off_23");
	quick.push("dis+1_2_bs=off:cond=on:drc=off:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=2.0:sagn=off:sac=on:sio=off:spl=sat:sser=off:ssnc=none:updr=off_35");
	quick.push("dis+2_5:1_bd=off:bs=off:ep=RSTC:gs=on:lcm=reverse:nwc=1.2:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:sac=on:sio=off:sfv=off:sp=reverse_arity_51");
	quick.push("dis-1002_5_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:spl=sat:ssfq=1.4:ssnc=none:updr=off_172");
	quick.push("dis-1010_2_bs=off:cond=fast:drc=off:nwc=1.7:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=backtracking:updr=off_120");
	quick.push("dis+2_4_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:nicw=on:ptb=off:ssec=off:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sgo=on:spl=backtracking:sp=reverse_arity_241");
	quick.push("ott+1_2_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=4:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_162");
      }
      else if (atoms > 20000) {
	quick.push("ott+1_4_bs=off:cond=on:drc=off:ep=on:flr=on:nwc=4:nicw=on:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:sos=on:sagn=off:spl=sat_16");
	quick.push("dis-1_1_bs=off:ep=RSTC:gs=on:nwc=1.1:sd=1:ss=included:st=5.0:sos=on:sio=off:sfv=off_7");
	quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=backtracking_12");
	quick.push("ott+2_5:1_bd=off:bs=off:drc=off:gsp=input_only:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:sos=on:spl=sat:urr=on_16");
	quick.push("dis+1_3:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=1.5:sos=on:sagn=off:sac=on:sio=off:spl=backtracking:sp=occurrence_11");
	quick.push("dis-1002_5_bs=off:drc=off:ep=on:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=1.2:sos=on:sagn=off:spl=sat:ssfq=1.4:ssnc=none_21");
	quick.push("ott+1_5:1_bs=off:br=off:cond=fast:drc=off:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=5.0:sos=all:sio=off:spl=sat:urr=on_10");
	quick.push("dis+1_2_bs=off:cond=on:drc=off:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=2.0:sagn=off:sac=on:sio=off:spl=sat:sser=off:ssnc=none:updr=off_10");
	quick.push("dis+1010_128_bs=off:cond=fast:drc=off:ep=on:flr=on:gs=on:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sswsr=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sac=on:sio=off:spo=on:spl=sat:sfv=off_14");
	quick.push("dis-2_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=3:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence:updr=off_53");
	quick.push("dis+10_5:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spl=sat:sp=reverse_arity_54");
	quick.push("dis-1010_14_bs=off:ep=RST:nwc=1.1:ptb=off:sd=1:ss=included:st=1.5:sos=on:sac=on:sio=off:spl=sat:ssfq=1.0:ssnc=none:sfv=off_11");
	quick.push("lrs+11_2:1_bs=off:cond=on:drc=off:ep=on:fde=none:gs=on:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:stl=30:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spo=on:spl=backtracking:urr=on_9");
	quick.push("dis-1010_1024_bs=off:cond=fast:drc=off:fde=none:lcm=reverse:nwc=4:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=sat_4");
	quick.push("dis+2_8:1_bs=off:drc=off:flr=on:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:spl=sat_10");
	quick.push("dis-3_5:1_bs=off:drc=off:ecs=on:ep=on:fde=none:gsp=input_only:nwc=1.3:ssec=off:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sac=on:sio=off:sp=occurrence_12");
	quick.push("dis+11_2:1_bs=off:ep=on:nwc=1:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:spl=sat_12");
	quick.push("ott+1011_8:1_bs=off:bsr=unit_only:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_221");
	quick.push("ott+1_2_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=4:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_70");
	quick.push("dis-1010_40_bs=off:cond=on:drc=off:gs=on:nwc=3:nicw=on:ptb=off:ssec=off:sd=4:ss=axioms:st=1.5:sos=on:sio=off:spl=sat_11");
	quick.push("dis-1010_2_bs=off:cond=fast:drc=off:nwc=1.7:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=backtracking:updr=off_134");
	quick.push("dis+3_4_bs=off:drc=off:ep=RST:fsr=off:nwc=3:ptb=off:ssec=off:sd=1:ss=axioms:st=1.5:sos=on:spl=sat:sser=off:ssfq=1.4:ssnc=none:sfv=off_16");
	quick.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=5:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_104");
	quick.push("ott+11_8:1_bs=off:drc=off:ecs=on:fsr=off:gs=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:sos=all:spl=sat:ssfq=2.0:ssnc=none_259");
	quick.push("dis+2_8:1_bd=off:bs=off:bsr=unit_only:drc=off:lcm=reverse:nwc=2.5:nicw=on:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=5:ss=axioms:st=1.5:sos=on:spl=sat:sp=reverse_arity_104");
	quick.push("dis-1010_5:4_bs=off:bms=on:drc=off:nwc=10:sd=2:ss=axioms:st=1.5:sac=on:sio=off:updr=off_221");
	quick.push("ott-3_50_bs=off:cond=fast:drc=off:flr=on:nwc=1.7:ptb=off:ssec=off:sd=2:ss=axioms:st=3.0:sos=on:sio=off:urr=on_10");
	quick.push("ott+4_5:1_bd=off:bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=3:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:urr=on_135");
      }
      else if (atoms > 5000) {
	quick.push("lrs+11_2:1_bs=off:cond=on:drc=off:ep=on:fde=none:gs=on:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:stl=30:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spo=on:spl=backtracking:urr=on_9");
	quick.push("dis-1_2:3_bs=off:drc=off:ecs=on:ep=RST:fde=none:gs=on:nwc=4:nicw=on:ssec=off:sos=on:sio=off:spl=off_3");
	quick.push("dis+1_2_bs=off:cond=on:drc=off:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=2.0:sagn=off:sac=on:sio=off:spl=sat:sser=off:ssnc=none:updr=off_6");
	quick.push("dis-1010_2_bs=off:cond=fast:drc=off:nwc=1.7:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=backtracking:updr=off_3");
	quick.push("dis+1011_3_bs=off:drc=off:fde=none:gs=on:nwc=1.1:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sio=off:spl=sat_11");
	quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=backtracking_22");
	quick.push("ott-1010_4_bs=off:cond=fast:drc=off:fsr=off:gs=on:nwc=10:nicw=on:ptb=off:ssec=off:sd=4:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spl=backtracking:sfv=off_4");
	quick.push("dis-1002_12_bs=off:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sswsr=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sio=off:spl=sat_4");
	quick.push("ott+1_2_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=4:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_21");
	quick.push("dis-1010_5:4_bs=off:bms=on:drc=off:nwc=10:sd=2:ss=axioms:st=1.5:sac=on:sio=off:updr=off_7");
	quick.push("ott+1011_8:1_bs=off:bsr=unit_only:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_56");
	quick.push("dis+1_5:1_bs=off:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sagn=off:spl=sat:ssfq=1.4:ssnc=none_33");
	quick.push("dis+2_8:1_bd=off:bs=off:bsr=unit_only:drc=off:lcm=reverse:nwc=2.5:nicw=on:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=5:ss=axioms:st=1.5:sos=on:spl=sat:sp=reverse_arity_29");
	quick.push("dis-1003_2:1_bs=off:drc=off:ep=on:fsr=off:fde=none:nwc=3:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:spl=sat_8");
	quick.push("dis+3_5_bs=off:drc=off:ep=RST:fsr=off:nwc=1.7:nicw=on:ptb=off:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:spl=sat:ssfq=1.4:ssnc=none:sfv=off_8");
	quick.push("ott+1_4_bs=off:cond=on:drc=off:ep=on:flr=on:nwc=4:nicw=on:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:sos=on:sagn=off:spl=sat_22");
	quick.push("ott+2_5:1_bd=off:bs=off:drc=off:gsp=input_only:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:sos=on:spl=sat:urr=on_23");
	quick.push("ott+1_5:1_bs=off:br=off:cond=fast:drc=off:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=5.0:sos=all:sio=off:spl=sat:urr=on_203");
	quick.push("dis+2_4_bs=off:drc=off:ep=RST:flr=on:lcm=reverse:nwc=1.7:ptb=off:ssec=off:sos=on:spl=sat:sp=reverse_arity_176");
	quick.push("dis+1011_2_bs=off:cond=on:drc=off:gs=on:nwc=4:ptb=off:ssec=off:sd=1:ss=axioms:st=1.2:spl=sat:updr=off_3");
	quick.push("ott-3_50_bs=off:cond=fast:drc=off:flr=on:nwc=1.7:ptb=off:ssec=off:sd=2:ss=axioms:st=3.0:sos=on:sio=off:urr=on_4");
	quick.push("dis-1002_5_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:spl=sat:ssfq=1.4:ssnc=none:updr=off_18");
	quick.push("ott+11_8:1_bs=off:drc=off:ecs=on:fsr=off:gs=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:sos=all:spl=sat:ssfq=2.0:ssnc=none_76");
      }
      else  {
	quick.push("dis-1010_5:1_bsr=on:drc=off:fde=none:gsp=input_only:gs=on:nwc=4:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:updr=off_15");
	quick.push("ott+1_2_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=4:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_25");
	quick.push("ott+2_8:1_bs=off:bsr=on:cond=fast:drc=off:fde=none:lcm=reverse:nwc=4:nicw=on:ptb=off:ssec=off:sos=on:spl=sat:sser=off:ssfp=100000:ssnc=none:urr=on_41");
	quick.push("dis+1011_2_bs=off:cond=fast:drc=off:fde=none:gs=on:nwc=4:ptb=off:ssec=off:sio=off:spl=backtracking:sp=occurrence_39");
	quick.push("ott+11_2:1_bs=off:cond=fast:drc=off:ep=RS:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=2.5:ptb=off:ssec=off:spl=sat:sp=occurrence_23");
	quick.push("dis+1_4_bs=off:drc=off:ep=on:fde=none:lcm=reverse:nwc=5:ptb=off:ssec=off:sos=on:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=reverse_arity_1");
	quick.push("dis+11_1_bs=off:bms=on:drc=off:ep=RS:flr=on:fde=none:nwc=5:sos=on:sgo=on:sio=off_22");
	quick.push("dis+1011_5:1_bs=off:cond=fast:drc=off:ep=RS:nwc=5:nicw=on:ptb=off:ssec=off:sio=off:spo=on_19");
	quick.push("ott+1_10_bs=off:cond=fast:drc=off:flr=on:lcm=predicate:nwc=10:ptb=off:ssec=off:sac=on:sio=off:spo=on:sp=occurrence:urr=on_8");
	quick.push("dis+2_8_bs=off:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sswn=on:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sp=occurrence_21");
	quick.push("ott+1011_8:1_bs=off:bsr=unit_only:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_285");
	quick.push("ott+1011_10_bd=off:bs=off:drc=off:ep=on:fde=none:gs=on:nwc=5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_86");
	quick.push("dis+10_64_bs=off:cond=on:drc=off:ep=RS:nwc=1:ptb=off:ssec=off:sio=off:spo=on_30");
	quick.push("ott-1002_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ep=RST:flr=on:fde=none:lcm=reverse:nwc=10:sac=on:sio=off:urr=on_83");
	quick.push("dis+11_4:1_bs=off:drc=off:ep=RST:fde=none:lcm=reverse:nwc=5:nicw=on:ssec=off:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sgo=on:sio=off:sp=occurrence_154");
	quick.push("ins-11_8:1_bs=off:bsr=unit_only:igbrr=0.9:igrr=1/128:igrp=400:igrpq=1.5:igwr=on:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sos=all:spl=off:sp=occurrence:updr=off_184");
	quick.push("ott-1004_3:1_bs=off:br=off:cond=on:drc=off:nwc=2:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat:urr=on_95");
	quick.push("dis+2_5:4_bs=off:br=off:cond=on:drc=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sio=off:spl=backtracking:urr=on_139");
	quick.push("dis+2_1_bs=off:bsr=unit_only:drc=off:fsr=off:gsp=input_only:gs=on:lcm=reverse:nwc=5:ptb=off:ssec=off:sswn=on:sd=2:sgt=7:ss=axioms:st=1.2:sos=on:sio=off:spl=sat_180");
	quick.push("dis+1011_3_bd=off:bs=off:drc=off:ep=on:fde=none:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_258");
	quick.push("dis-1010_14_bs=off:ep=RST:nwc=1.1:ptb=off:sd=1:ss=included:st=1.5:sos=on:sac=on:sio=off:spl=sat:ssfq=1.0:ssnc=none:sfv=off_19");
	quick.push("ott+1_8:1_bd=off:bs=off:drc=off:fde=none:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sos=on:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=reverse_arity_26");
      }
    }
    else if (prop == 0) {
      if (atoms <= 70) {
	quick.push("ott+10_3:1_bsr=unit_only:cond=on:fsr=off:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat:urr=on:updr=off_21");
	quick.push("lrs+10_8_bs=off:drc=off:gs=on:nwc=1.5:nicw=on:ptb=off:ssec=off:stl=60:sio=off:spo=on:spl=sat:updr=off_11");
	quick.push("ott+2_8_bd=off:bs=off:bsr=unit_only:cond=on:flr=on:nwc=2:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:updr=off_59");
	quick.push("dis+1_16_bd=off:bs=off:cond=fast:drc=off:fsr=off:nwc=1.2:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:urr=on_72");
	quick.push("lrs+2_40_bs=off:cond=fast:drc=off:nwc=1.7:ptb=off:ssec=off:stl=30:sio=off:spo=on:spl=sat_181");
	quick.push("ott-1003_2:1_bs=unit_only:bsr=unit_only:drc=off:nwc=1.2:ptb=off:ssec=off:sio=off:updr=off_52");
	quick.push("dis+2_12_drc=off:ep=RST:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:spl=sat:sp=occurrence_57");
	quick.push("ott+4_64_bs=off:drc=off:flr=on:lcm=predicate:nwc=10:ptb=off:ssec=off:spl=sat:sp=reverse_arity_108");
	quick.push("ott+3_28_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sac=on:sio=off_89");
	quick.push("dis+1_2_bs=off:cond=on:drc=off:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=2.0:sagn=off:sac=on:sio=off:spl=sat:sser=off:ssnc=none:updr=off_97");
	quick.push("ott-11_8:1_bd=off:bs=off:drc=off:lcm=reverse:nwc=3:sio=off:spl=off:urr=on_105");
	quick.push("ott+11_3_bd=off:bs=off:gs=on:nwc=1.1:nicw=on:ptb=off:ssec=off:spl=sat:sser=off:ssfp=10000:ssfq=2.0_272");
	quick.push("ott+3_3_bs=off:bsr=unit_only:cond=fast:drc=off:fsr=off:fde=none:gs=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sgo=on:spo=on:spl=backtracking:sp=occurrence_338");
      }
      else {
	quick.push("ott+1011_1_bs=off:cond=on:drc=off:ecs=on:nwc=2:nicw=on:ptb=off:ssec=off:spl=sat:ssfp=1000:ssfq=1.2:ssnc=none_18");
	quick.push("dis-4_3:2_cond=on:drc=off:gs=on:nwc=4:nicw=on:ptb=off:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence_2");
	quick.push("dis-1_6_bs=off:bsr=unit_only:cond=on:drc=off:fsr=off:gs=on:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sos=on:sio=off:spo=on:urr=on_24");
	quick.push("ott+1_10_bs=off:cond=fast:drc=off:flr=on:lcm=predicate:nwc=10:ptb=off:ssec=off:sac=on:sio=off:spo=on:sp=occurrence:urr=on_121");
	quick.push("dis-1002_5:1_bs=off:bms=on:drc=off:ecs=on:flr=on:gs=on:nwc=10:nicw=on:ssec=off:sac=on:sgo=on:urr=on_9");
	quick.push("ott+1_12_bs=off:br=off:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat:sser=off:ssfq=1.0:ssnc=none:urr=on_95");
	quick.push("ott-1004_3:2_br=off:drc=off:fsr=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sos=all:spl=sat:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_194");
	quick.push("lrs+1_20_bs=off:cond=fast:gs=on:nwc=4:ptb=off:ssec=off:sswsr=on:stl=30:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sio=off:spo=on:spl=backtracking:updr=off_228");
	quick.push("ott+10_64_bd=off:bs=off:cond=on:drc=off:ecs=on:gs=on:nwc=1:ssec=off:sac=on:sio=off_267");
	quick.push("lrs-1004_50_bs=off:br=off:cond=fast:drc=off:nwc=1.5:nicw=on:stl=60:sio=off:spl=off:urr=on:updr=off_148");
	quick.push("lrs-3_10_drc=off:nwc=5:ptb=off:ssec=off:stl=30:spl=sat:sser=off:ssfp=4000:ssnc=none:urr=on_150");
	quick.push("lrs+1_4_bs=off:drc=off:ecs=on:ep=on:flr=on:fsr=off:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=30:spl=sat:sser=off:ssfp=40000:ssfq=1.1:ssnc=none:sp=occurrence_154");
	quick.push("ott+11_10_bd=off:bs=off:cond=fast:drc=off:lcm=predicate:nwc=1:nicw=on:sac=on:sgo=on:urr=on_333");
	quick.push("dis+2_5:4_bs=off:br=off:cond=on:drc=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sio=off:spl=backtracking:urr=on_3");
	quick.push("ott-1003_24_bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:ptb=off:ssec=off:spl=sat:sser=off:ssfp=1000:ssnc=none:urr=on_51");
      }
    }
    else if (prop == 131075) {
      if (atoms > 3000) {
	quick.push("dis-1002_3_bs=off:cond=fast:drc=off:ep=RS:nwc=1.1:ptb=off:ssec=off:swb=on_22");
	quick.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=backtracking_5");
	quick.push("dis-1_1_bs=off:ep=RSTC:gs=on:nwc=1.1:sd=1:ss=included:st=5.0:sos=on:sio=off:sfv=off_6");
	quick.push("ott+4_3:1_bs=off:bms=on:br=off:drc=off:fde=none:nwc=1.7:nicw=on:sd=3:ss=axioms:st=3.0:sos=all:sio=off:spl=off:sfv=off:urr=on_14");
	quick.push("ott+1011_1_bs=off:cond=on:drc=off:ecs=on:nwc=2:nicw=on:ptb=off:ssec=off:spl=sat:ssfp=1000:ssfq=1.2:ssnc=none_69");
	quick.push("ott-1002_5:4_bs=off:drc=off:fde=none:nwc=1.7:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:spl=sat:urr=on_16");
	quick.push("dis+11_8:1_bs=off:br=off:cond=on:drc=off:ecs=on:ep=RST:fsr=off:nwc=1:ptb=off:ssec=off:sd=7:ss=axioms:st=2.0:sio=off:spo=on:spl=sat:ssnc=none:urr=on:updr=off_29");
	quick.push("dis+2_8:1_bs=off:drc=off:flr=on:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:spl=sat_36");
	quick.push("dis+2_8:1_bd=off:bs=off:bsr=unit_only:drc=off:lcm=reverse:nwc=2.5:nicw=on:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=5:ss=axioms:st=1.5:sos=on:spl=sat:sp=reverse_arity_62");
	quick.push("dis+1_3:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=1.5:sos=on:sagn=off:sac=on:sio=off:spl=backtracking:sp=occurrence_157");
	quick.push("lrs+1_4_bs=off:drc=off:ecs=on:ep=on:flr=on:fsr=off:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=30:spl=sat:sser=off:ssfp=40000:ssfq=1.1:ssnc=none:sp=occurrence_164");
	quick.push("ott-1010_8:1_bs=off:flr=on:fsr=off:gs=on:nwc=4:ptb=off:ssec=off:sac=on:sio=off:sp=reverse_arity:urr=on_434");
	quick.push("dis-1010_7_bs=off:cond=fast:drc=off:fde=none:nwc=2:ptb=off:ssec=off:spo=on:sp=occurrence_237");
      }
      else {
	quick.push("ott-1002_5:4_bs=off:drc=off:fde=none:nwc=1.7:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:spl=sat:urr=on_1");
	quick.push("dis-1010_5:4_bs=off:bms=on:drc=off:nwc=10:sd=2:ss=axioms:st=1.5:sac=on:sio=off:updr=off_1");
	quick.push("ott-1002_1024_bd=off:bs=off:cond=on:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sos=on:sgo=on:sio=off:spo=on:spl=backtracking:urr=on_8");
	quick.push("ott+1011_10_bd=off:bs=off:drc=off:ep=on:fde=none:gs=on:nwc=5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_5");
	quick.push("dis+1011_1_bs=off:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1.7:nicw=on:ptb=off:ssec=off:sgt=7:ss=axioms:sos=on:spl=sat_4");
	quick.push("dis-1002_5_bs=off:drc=off:ep=on:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=1.2:sos=on:sagn=off:spl=sat:ssfq=1.4:ssnc=none_4");
	quick.push("ott-11_4:1_bs=off:bsr=on:cond=fast:drc=off:ecs=on:nwc=1.3:ssec=off:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sio=off_3");
	quick.push("ott+3_3_bs=off:bsr=unit_only:cond=fast:drc=off:fsr=off:fde=none:gs=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sgo=on:spo=on:spl=backtracking:sp=occurrence_14");
	quick.push("ott+11_8:1_bd=off:bs=unit_only:bsr=unit_only:drc=off:fsr=off:lcm=reverse:nwc=1.1:nicw=on:ptb=off:ssec=off:spl=sat:ssfq=2.0:ssnc=none_17");
	quick.push("ott+11_64_bd=off:bs=off:br=off:cond=fast:drc=off:ep=on:gsp=input_only:gs=on:nwc=2:ptb=off:ssec=off:sos=all:sio=off:spl=backtracking:urr=on_9");
	quick.push("dis+1010_7_bs=off:bsr=on:bms=on:drc=off:fsr=off:fde=none:gs=on:nwc=1.7:sac=on:sgo=on:sio=off:sp=occurrence_57");
	quick.push("ott+4_3:1_bs=off:bms=on:br=off:drc=off:fde=none:nwc=1.7:nicw=on:sd=3:ss=axioms:st=3.0:sos=all:sio=off:spl=off:sfv=off:urr=on_1");
	quick.push("dis-1002_5_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:spl=sat:ssfq=1.4:ssnc=none:updr=off_11");
	quick.push("ott-4_7_bs=off:drc=off:fde=none:gs=on:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=backtracking:urr=on_13");
	quick.push("ott+11_50_bd=off:bs=off:cond=fast:drc=off:ep=on:fsr=off:lcm=reverse:nwc=1:nicw=on:ptb=off:ssec=off:sos=on:spl=backtracking:sp=occurrence:updr=off_10");
	quick.push("dis-1_1_bs=off:ep=RSTC:gs=on:nwc=1.1:sd=1:ss=included:st=5.0:sos=on:sio=off:sfv=off_1");
	quick.push("ott-11_8:1_bd=off:bs=off:drc=off:lcm=reverse:nwc=3:sio=off:spl=off:urr=on_118");
	quick.push("dis-1010_1024_bs=off:cond=fast:drc=off:fde=none:lcm=reverse:nwc=4:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=sat_1");
	quick.push("dis-1010_7_bs=off:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:updr=off_123");
	quick.push("ott-2_5:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking_11");
	quick.push("dis+1011_2_bs=off:cond=on:drc=off:gs=on:nwc=4:ptb=off:ssec=off:sd=1:ss=axioms:st=1.2:spl=sat:updr=off_8");
	quick.push("dis+1011_3_bd=off:bs=off:drc=off:ep=on:fde=none:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_174");
	quick.push("ott-1010_24_bd=off:bs=off:drc=off:fsr=off:gs=on:nwc=4:nicw=on:ptb=off:ssec=off:spl=backtracking_76");
	quick.push("ins-11_8:1_bs=off:bsr=unit_only:igbrr=0.9:igrr=1/128:igrp=400:igrpq=1.5:igwr=on:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sos=all:spl=off:sp=occurrence:updr=off_67");
	quick.push("ott+1011_1_bs=off:cond=on:drc=off:ecs=on:nwc=2:nicw=on:ptb=off:ssec=off:spl=sat:ssfp=1000:ssfq=1.2:ssnc=none_190");
	quick.push("dis-1010_5:1_bsr=on:drc=off:fde=none:gsp=input_only:gs=on:nwc=4:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:updr=off_170");
	quick.push("lrs-2_2:1_bs=off:br=off:cond=on:ep=on:fde=none:lcm=reverse:nwc=10:ptb=off:ssec=off:stl=60:sos=on:sio=off:spo=on:urr=on_327");
	quick.push("dis-1010_2_bs=off:cond=fast:drc=off:nwc=1.7:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=backtracking:updr=off_9");
	quick.push("dis+1010_24_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=2.5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_65");
      }
    }
    else if (prop == 131073) {
      if (atoms > 200) {
	quick.push("dis+1011_2_bs=off:cond=fast:drc=off:fde=none:gs=on:nwc=4:ptb=off:ssec=off:sio=off:spl=backtracking:sp=occurrence_1");
	quick.push("ott-3_50_bs=off:cond=fast:drc=off:flr=on:nwc=1.7:ptb=off:ssec=off:sd=2:ss=axioms:st=3.0:sos=on:sio=off:urr=on_2");
	quick.push("ott-1010_4_bs=off:cond=fast:drc=off:fsr=off:gs=on:nwc=10:nicw=on:ptb=off:ssec=off:sd=4:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spl=backtracking:sfv=off_2");
	quick.push("dis+1010_24_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=2.5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_5");
	quick.push("dis+1_4:1_bs=off:drc=off:ep=on:fde=none:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:spl=sat:sp=reverse_arity:updr=off_1");
	quick.push("ott+1011_8:1_bs=off:bsr=unit_only:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_2");
	quick.push("ott+1_8:1_bs=off:drc=off:ep=on:flr=on:gsp=input_only:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spl=backtracking_1");
	quick.push("dis+1_14_bs=off:br=off:drc=off:fde=none:gs=on:nwc=1.1:ssec=off:sd=2:ss=axioms:st=2.0:sac=on:sio=off:urr=on_2");
	quick.push("dis+1011_1_bs=off:bsr=on:cond=fast:drc=off:flr=on:fde=none:gs=on:nwc=1.5:ptb=off:ssec=off:sos=on:sac=on:sio=off:urr=on_20");
	quick.push("dis-1002_1024_bs=off:bms=on:cond=fast:drc=off:ecs=on:ep=on:lcm=predicate:nwc=3:nicw=on:ssec=off:sswn=on:sswsr=on:sac=on_1");
	quick.push("ins+1011_3:1_bs=off:cond=fast:ep=RSTC:igbrr=0.8:igrr=1/2:igrp=200:igrpq=1.0:igwr=on:nwc=2:ptb=off:ssec=off:sos=all:sio=off:spl=off_8");
	quick.push("ott-2_5:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking_2");
	quick.push("dis+1011_14_bd=off:bs=off:drc=off:nwc=4:ptb=off:ssec=off:sswn=on:sac=on:spl=sat:sp=occurrence_16");
	quick.push("dis+1011_12_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.5:ptb=off:ssec=off:spl=sat_28");
	quick.push("lrs-1004_50_bs=off:br=off:cond=fast:drc=off:nwc=1.5:nicw=on:stl=60:sio=off:spl=off:urr=on:updr=off_5");
	quick.push("dis-1010_50_bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:ptb=off:sswn=on:sswsr=on:spl=sat:sser=off:ssfp=40000:ssfq=1.0:ssnc=none_3");
	quick.push("ott-1004_3:1_bs=off:br=off:cond=on:drc=off:nwc=2:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat:urr=on_8");
	quick.push("ott+11_12_cond=fast:drc=off:ecs=on:gs=on:nwc=1.2:nicw=on:ssec=off:sp=occurrence_1");
	quick.push("dis+1010_7_bs=off:bsr=on:bms=on:drc=off:fsr=off:fde=none:gs=on:nwc=1.7:sac=on:sgo=on:sio=off:sp=occurrence_2");
	quick.push("dis+1_64_bs=off:drc=off:fde=none:nwc=3:nicw=on:sos=on:sio=off:sp=reverse_arity:urr=on_16");
	quick.push("dis+11_2:1_bs=off:cond=fast:drc=off:fde=none:gs=on:nwc=2:nicw=on:ptb=off:ssec=off:sos=all:sac=on:sio=off:spo=on:spl=sat:sscc=on:sser=off:ssfq=2.0:sp=occurrence_18");
	quick.push("dis-1010_5:1_bsr=on:drc=off:fde=none:gsp=input_only:gs=on:nwc=4:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:updr=off_18");
	quick.push("dis-1003_2:1_bs=off:drc=off:ep=on:fsr=off:fde=none:nwc=3:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:spl=sat_2");
	quick.push("ins-1003_3_bs=off:ep=RSTC:flr=on:gsp=input_only:igbrr=0.0:igrr=1/128:igrp=1400:igrpq=2.0:igwr=on:nwc=2:ptb=off:ssec=off:sos=on:sio=off:spl=off_2");
	quick.push("lrs+11_2:1_bs=off:cond=on:drc=off:ep=on:fde=none:gs=on:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:stl=30:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spo=on:spl=backtracking:urr=on_1");
	quick.push("dis+1_2_bs=off:cond=on:drc=off:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=2.0:sagn=off:sac=on:sio=off:spl=sat:sser=off:ssnc=none:updr=off_4");
	quick.push("lrs+1_14_bs=off:cond=fast:drc=off:nwc=1.3:nicw=on:ssec=off:stl=60:spo=on:updr=off_1");
	quick.push("dis-1002_3_bs=off:cond=fast:drc=off:ep=RS:nwc=1.1:ptb=off:ssec=off:swb=on_8");
	quick.push("dis+2_4_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:nicw=on:ptb=off:ssec=off:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sgo=on:spl=backtracking:sp=reverse_arity_16");
	quick.push("dis+1_3:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=1.5:sos=on:sagn=off:sac=on:sio=off:spl=backtracking:sp=occurrence_1");
	quick.push("dis+2_8_bs=off:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sswn=on:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sp=occurrence_30");
	quick.push("dis-1002_5_bs=off:cond=on:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:spl=sat:ssfq=1.4:ssnc=none:updr=off_13");
	quick.push("dis+10_128_bd=off:bs=off:drc=off:nwc=3:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking_29");
	quick.push("dis+2_5_bs=off:cond=fast:drc=off:nwc=1.3:nicw=on:ptb=off:ssec=off:ss=included:st=1.5:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_13");
	quick.push("ott+1_2_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=4:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_42");
	quick.push("ott+3_24_bs=unit_only:drc=off:ecs=on:fde=none:nwc=1.1:ssec=off:sos=all:sac=on_2");
	quick.push("dis+11_8:1_bs=off:br=off:cond=on:drc=off:ecs=on:ep=RST:fsr=off:nwc=1.1:ptb=off:ssec=off:sd=5:ss=axioms:st=3.0:sio=off:spo=on:spl=sat:ssfq=1.2:ssnc=none:urr=on_97");
	quick.push("dis-2_8:1_bs=off:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sswn=on:sswsr=on:sgt=10:ss=axioms:sos=on:spl=sat_93");
	quick.push("dis+1011_64_bs=off:drc=off:fde=none:lcm=predicate:nwc=5:nicw=on:ssec=off:sswn=on:sp=reverse_arity_257");
	quick.push("ott-1010_8:1_bs=off:flr=on:fsr=off:gs=on:nwc=4:ptb=off:ssec=off:sac=on:sio=off:sp=reverse_arity:urr=on_1");
	quick.push("dis+1_2:1_bd=off:bs=off:bsr=on:drc=off:ep=on:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sio=off:spo=on:spl=backtracking_1");
	quick.push("ott+3_28_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sac=on:sio=off_2");
	quick.push("dis+1011_1_bs=off:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1.7:nicw=on:ptb=off:ssec=off:sgt=7:ss=axioms:sos=on:spl=sat_2");
	quick.push("ott+4_3:1_bs=off:bms=on:br=off:drc=off:fde=none:nwc=1.7:nicw=on:sd=3:ss=axioms:st=3.0:sos=all:sio=off:spl=off:sfv=off:urr=on_2");
	quick.push("lrs-2_2:1_bs=off:br=off:cond=on:ep=on:fde=none:lcm=reverse:nwc=10:ptb=off:ssec=off:stl=60:sos=on:sio=off:spo=on:urr=on_4");
	quick.push("ott+2_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ecs=on:ep=RST:flr=on:fde=none:lcm=reverse:nwc=5:ssec=off:sac=on:sio=off:urr=on_4");
	quick.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=5:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_8");
	quick.push("dis-3_5:1_bs=off:drc=off:ecs=on:ep=on:fde=none:gsp=input_only:nwc=1.3:ssec=off:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sac=on:sio=off:sp=occurrence_9");
	quick.push("ott+11_2:1_bs=off:cond=fast:drc=off:ep=RS:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=2.5:ptb=off:ssec=off:spl=sat:sp=occurrence_12");
	quick.push("dis+1011_3_bs=off:drc=off:fde=none:nwc=10:nicw=on:ss=axioms:st=2.0:sac=on:sio=off_16");
	quick.push("dis+11_8_bs=off:cond=fast:ep=RST:fsr=off:gsp=input_only:lcm=predicate:nwc=1.2:ptb=off:sd=7:ss=axioms:st=2.0:sgo=on:spo=on:spl=sat:sser=off:ssfq=1.1:ssnc=none_16");
	quick.push("dis+11_8:1_bs=off:br=off:cond=on:drc=off:ecs=on:ep=RST:fsr=off:nwc=1:ptb=off:ssec=off:sd=7:ss=axioms:st=2.0:sio=off:spo=on:spl=sat:ssnc=none:urr=on:updr=off_18");
	quick.push("ott+1011_1_bs=off:cond=on:drc=off:ecs=on:nwc=2:nicw=on:ptb=off:ssec=off:spl=sat:ssfp=1000:ssfq=1.2:ssnc=none_19");
	quick.push("dis-1003_50_bs=off:cond=fast:drc=off:fde=none:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sos=on:sgo=on:sio=off:spo=on:spl=sat_24");
	quick.push("dis+1011_3_bs=off:drc=off:fde=none:gs=on:nwc=1.1:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sio=off:spl=sat_24");
	quick.push("dis-1010_7_bs=off:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:updr=off_59");
	quick.push("dis+1010_32_cond=fast:drc=off:ep=RS:fsr=off:nwc=1.7:ptb=off:ssec=off:spl=sat_61");
	quick.push("ott-1002_1024_bd=off:bs=off:cond=on:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sos=on:sgo=on:sio=off:spo=on:spl=backtracking:urr=on_62");
	quick.push("dis-1010_1024_bs=off:cond=fast:drc=off:fde=none:lcm=reverse:nwc=4:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=sat_83");
      }
      else {
	quick.push("dis-1010_5:4_bs=off:bms=on:drc=off:nwc=10:sd=2:ss=axioms:st=1.5:sac=on:sio=off:updr=off_14");
	quick.push("ott-2_5:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking_3");
	quick.push("ott-1004_3:1_bs=off:br=off:cond=on:drc=off:nwc=2:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat:urr=on_9");
	quick.push("dis-1010_2_bs=off:cond=fast:drc=off:nwc=1.7:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=backtracking:updr=off_22");
	quick.push("dis+1_2_bs=off:cond=on:drc=off:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=2.0:sagn=off:sac=on:sio=off:spl=sat:sser=off:ssnc=none:updr=off_5");
	quick.push("dis+1011_3_bd=off:bs=off:drc=off:ep=on:fde=none:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_2");
	quick.push("ott-4_7_bs=off:drc=off:fde=none:gs=on:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=backtracking:urr=on_4");
	quick.push("ott+3_32_bd=off:bs=off:drc=off:flr=on:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:spl=sat:updr=off_3");
	quick.push("ott+1011_5:1_bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=backtracking:sp=occurrence_2");
	quick.push("dis+1010_24_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=2.5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_116");
	quick.push("dis+2_4_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:nicw=on:ptb=off:ssec=off:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sgo=on:spl=backtracking:sp=reverse_arity_46");
	quick.push("dis+2_8_bs=off:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sswn=on:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=sat:sp=occurrence_38");
	quick.push("lrs+1003_8:1_bs=off:drc=off:ep=on:fsr=off:gsp=input_only:gs=on:nwc=1.5:ptb=off:ssec=off:stl=30:sio=off:spl=sat_113");
	quick.push("ott+11_8:1_bs=off:drc=off:ecs=on:fsr=off:gs=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:sos=all:spl=sat:ssfq=2.0:ssnc=none_65");
	quick.push("dis+10_128_bd=off:bs=off:drc=off:nwc=3:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking_99");
	quick.push("dis+1011_3_bs=off:drc=off:fde=none:gs=on:nwc=1.1:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sio=off:spl=sat_121");
	quick.push("dis+1011_14_bd=off:bs=off:drc=off:nwc=4:ptb=off:ssec=off:sswn=on:sac=on:spl=sat:sp=occurrence_219");
	quick.push("ins+1011_3:1_bs=off:cond=fast:ep=RSTC:igbrr=0.8:igrr=1/2:igrp=200:igrpq=1.0:igwr=on:nwc=2:ptb=off:ssec=off:sos=all:sio=off:spl=off_4");
	quick.push("ott+11_12_cond=fast:drc=off:ecs=on:gs=on:nwc=1.2:nicw=on:ssec=off:sp=occurrence_11");
      }
    }
    else if (prop == 131081 || prop == 131072) {
      quick.push("dis+11_2:1_bs=off:cond=fast:drc=off:fde=none:gs=on:nwc=2:nicw=on:ptb=off:ssec=off:sos=all:sac=on:sio=off:spo=on:spl=sat:sscc=on:sser=off:ssfq=2.0:sp=occurrence_1");
      quick.push("ott+1_5:1_bs=off:cond=fast:drc=off:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:sos=on:spl=sat:sp=occurrence_24");
      quick.push("dis-1010_7_bs=off:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:updr=off_11");
      quick.push("dis-1003_50_bs=off:cond=fast:drc=off:fde=none:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sos=on:sgo=on:sio=off:spo=on:spl=sat_1");
      quick.push("ott-1010_8:1_bs=off:flr=on:fsr=off:gs=on:nwc=4:ptb=off:ssec=off:sac=on:sio=off:sp=reverse_arity:urr=on_6");
      quick.push("ott+1011_5:1_bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=backtracking:sp=occurrence_141");
      quick.push("dis+1_20_bd=off:bs=off:drc=off:ep=on:flr=on:lcm=predicate:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:ss=included:st=5.0:sos=on:sagn=off:spl=sat:ssnc=none_28");
      quick.push("dis+1010_128_bs=off:cond=fast:drc=off:ep=on:flr=on:gs=on:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sswsr=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sac=on:sio=off:spo=on:spl=sat:sfv=off_25");
      quick.push("dis+1011_3_bs=off:drc=off:fde=none:gs=on:nwc=1.1:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sio=off:spl=sat_31");
      quick.push("ins-11_8:1_bs=off:bsr=unit_only:igbrr=0.9:igrr=1/128:igrp=400:igrpq=1.5:igwr=on:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sos=all:spl=off:sp=occurrence:updr=off_160");
      quick.push("dis+1_16_bd=off:bs=off:cond=fast:drc=off:fsr=off:nwc=1.2:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:urr=on_106");
      quick.push("lrs+1_4_bs=off:drc=off:ecs=on:ep=on:flr=on:fsr=off:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=30:spl=sat:sser=off:ssfp=40000:ssfq=1.1:ssnc=none:sp=occurrence_96");
      quick.push("dis-1010_3_bs=off:drc=off:fde=none:nwc=1:nicw=on:ptb=off:ssec=off:sd=1:ss=axioms:st=3.0:sac=on:sio=off:spl=sat_190");
      quick.push("dis+1_3:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=1.5:sos=on:sagn=off:sac=on:sio=off:spl=backtracking:sp=occurrence_201");
      quick.push("dis+2_5:4_bs=off:br=off:cond=on:drc=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sio=off:spl=backtracking:urr=on_219");
      quick.push("ott+1011_10_bd=off:bs=off:drc=off:ep=on:fde=none:gs=on:nwc=5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_228");
      quick.push("ott-2_5:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking_1");
    }
    else if (prop > 255) {
      quick.push("ott+1_2_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=4:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_21");
      quick.push("dis+1_16_bd=off:bs=off:cond=fast:drc=off:fsr=off:nwc=1.2:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:urr=on_112");
      quick.push("dis+10_64_bd=off:bs=off:cond=fast:drc=off:ep=RSTC:flr=on:gsp=input_only:nwc=4:nicw=on:ptb=off:ssec=off:sswn=on:sd=10:ss=included:st=2.0:sos=all:spl=backtracking_56");
      quick.push("ott-1010_8:1_bs=off:flr=on:fsr=off:gs=on:nwc=4:ptb=off:ssec=off:sac=on:sio=off:sp=reverse_arity:urr=on_22");
      quick.push("dis-1_2:3_bs=off:drc=off:ecs=on:ep=RST:fde=none:gs=on:nwc=4:nicw=on:ssec=off:sos=on:sio=off:spl=off_23");
      quick.push("ott+1_8_bs=off:drc=off:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_76");
      quick.push("dis-1010_3_bs=off:drc=off:fde=none:nwc=1:nicw=on:ptb=off:ssec=off:sd=1:ss=axioms:st=3.0:sac=on:sio=off:spl=sat_56");
      quick.push("dis-1010_7_bs=off:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:updr=off_227");
      quick.push("dis+1011_3_bs=off:drc=off:fde=none:nwc=10:nicw=on:ss=axioms:st=2.0:sac=on:sio=off_75");
      quick.push("dis+1002_5:1_bs=off:bms=on:drc=off:ep=on:flr=on:fde=none:gsp=input_only:nwc=1:nicw=on:ssec=off:sac=on:sio=off:updr=off_388");
      quick.push("dis+1_2:1_bs=off:bms=on:br=off:drc=off:gsp=input_only:gs=on:lcm=predicate:nwc=1:nicw=on:ssec=off:sd=3:sgt=7:ss=axioms:st=2.0:sos=on:spo=on:urr=on_202");
    }
    else {
      quick.push("dis+1011_14_bd=off:bs=off:drc=off:nwc=4:ptb=off:ssec=off:sswn=on:sac=on:spl=sat:sp=occurrence_7");
      quick.push("ins+10_4:1_bs=off:bsr=unit_only:cond=on:ep=RSTC:gs=on:igbrr=0.4:igrr=1/128:igrp=100:igrpq=1.3:igwr=on:nwc=1.1:ptb=off:ssec=off:sos=on:sio=off:spl=off:urr=on_2");
      quick.push("lrs+1003_8:1_bs=off:bsr=unit_only:cond=fast:drc=off:flr=on:fsr=off:gsp=input_only:gs=on:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:stl=90:sgo=on:sio=off:spl=backtracking:sp=occurrence:urr=on_7");
      quick.push("dis+1_3:1_bs=off:drc=off:fde=none:gs=on:nwc=1.7:ptb=off:ssec=off:sos=all:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence_1");
      quick.push("ott+11_12_cond=fast:drc=off:ecs=on:gs=on:nwc=1.2:nicw=on:ssec=off:sp=occurrence_4");
      quick.push("ott-1_2:3_bs=off:bms=on:cond=on:drc=off:fde=none:lcm=predicate:nwc=1.7:nicw=on:sd=5:ss=axioms:st=1.2:sio=off:urr=on_23");
      quick.push("dis+1_16_bd=off:bs=off:cond=fast:drc=off:fsr=off:nwc=1.2:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:urr=on_2");
      quick.push("ott+2_8:1_bs=off:bsr=on:cond=fast:drc=off:fde=none:lcm=reverse:nwc=4:nicw=on:ptb=off:ssec=off:sos=on:spl=sat:sser=off:ssfp=100000:ssnc=none:urr=on_24");
      quick.push("dis+2_5_bs=off:cond=fast:drc=off:nwc=1.3:nicw=on:ptb=off:ssec=off:ss=included:st=1.5:sio=off:spl=sat:sser=off:ssfq=1.4:ssnc=none_1");
      quick.push("dis+11_16_bs=off:drc=off:gs=on:nwc=5:nicw=on:ptb=off:ssec=off:sos=on:sio=off:spo=on:spl=sat:sser=off:ssfp=1000:ssnc=none:sp=occurrence:urr=on_2");
      quick.push("lrs+1003_8:1_bs=off:drc=off:ep=on:fsr=off:gsp=input_only:gs=on:nwc=1.5:ptb=off:ssec=off:stl=30:sio=off:spl=sat_28");
      quick.push("dis+2_40_bs=off:drc=off:gs=on:lcm=predicate:nwc=5:ptb=off:ssec=off:sd=1:sgt=7:ss=axioms:sac=on:sgo=on:sio=off:spl=sat:sp=occurrence_2");
      quick.push("dis-1002_5:1_bs=off:bms=on:drc=off:ecs=on:flr=on:gs=on:nwc=10:nicw=on:ssec=off:sac=on:sgo=on:urr=on_1");
      quick.push("dis+1011_12_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.5:ptb=off:ssec=off:spl=sat_1");
      quick.push("dis-1010_3_bs=off:drc=off:fde=none:nwc=1:nicw=on:ptb=off:ssec=off:sd=1:ss=axioms:st=3.0:sac=on:sio=off:spl=sat_13");
      quick.push("dis-1010_7_bs=off:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:updr=off_41");
      quick.push("dis+1011_5_bs=off:bms=on:drc=off:fde=none:nwc=1.5:nicw=on:ssec=off:sswn=on:sswsr=on:sd=3:sgt=5:ss=axioms:st=3.0:sos=on:sagn=off:sgo=on:spo=on:sp=reverse_arity_21");
      quick.push("dis+2_128_bs=off:bms=on:drc=off:fde=none:lcm=reverse:nwc=1.3:nicw=on:ssec=off:sos=on:sio=off:spl=off_2");
      quick.push("dis+11_2:3_bs=off:bsr=unit_only:drc=off:gs=on:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sos=on:spl=sat:sp=reverse_arity:urr=on:updr=off_15");
      quick.push("ott+1011_8:1_bs=off:bsr=unit_only:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_236");
      quick.push("dis+1011_64_bs=off:drc=off:fde=none:lcm=predicate:nwc=5:nicw=on:ssec=off:sswn=on:sp=reverse_arity_71");
      quick.push("ott+10_5:1_bd=off:bs=off:cond=fast:drc=off:gsp=input_only:lcm=reverse:nwc=4:nicw=on:ptb=off:ssec=off:ss=axioms:st=3.0:sos=on:sio=off:spo=on:spl=sat:urr=on_1");
      quick.push("ins+1011_3:1_bs=off:cond=fast:ep=RSTC:igbrr=0.8:igrr=1/2:igrp=200:igrpq=1.0:igwr=on:nwc=2:ptb=off:ssec=off:sos=all:sio=off:spl=off_232");
      quick.push("dis+3_4_bd=off:bs=off:cond=fast:drc=off:fsr=off:fde=none:gs=on:lcm=reverse:nwc=1.7:ptb=off:ssec=off:sos=on:spl=sat_39");
      quick.push("dis+1011_3_bs=off:drc=off:fde=none:gs=on:nwc=1.1:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sio=off:spl=sat_178");
      quick.push("dis+11_2:1_bs=off:cond=fast:drc=off:fde=none:gs=on:nwc=2:nicw=on:ptb=off:ssec=off:sos=all:sac=on:sio=off:spo=on:spl=sat:sscc=on:sser=off:ssfq=2.0:sp=occurrence_52");
      quick.push("lrs+3_8:1_bsr=on:cond=on:drc=off:flr=on:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:stl=90:sgo=on:sio=off:spl=backtracking:sp=reverse_arity:urr=on_370");
      quick.push("dis-1002_3_bs=off:cond=on:drc=off:gs=on:nwc=3:nicw=on:ssec=off:sgo=on:sio=off:sp=reverse_arity_21");
      quick.push("ott+1011_5:1_bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=backtracking:sp=occurrence_73");
      quick.push("ott+1010_2:3_bs=off:drc=off:fde=none:nwc=1.2:sac=on_81");
    }
    break;

  case Property::FNE:
    if (prop == 0) {
      if (atoms > 400) {
	quick.push("ott+11_14_bs=off:drc=off:ep=RS:flr=on:fde=none:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sio=off:spo=on_6");
	quick.push("dis+3_2_bs=off:gs=on:nwc=2.5:ptb=off:ssec=off:sac=on:spl=sat:sp=reverse_arity_1");
	quick.push("dis+3_7_bs=off:bms=on:cond=fast:ecs=on:fsr=off:lcm=reverse:nwc=1.1:ssec=off_54");
	quick.push("dis+1004_5_bs=off:nwc=4:nicw=on:ptb=off:ssec=off:sagn=off:spl=backtracking_129");
	quick.push("dis+11_40_bs=off:bsr=on:cond=on:fsr=off:lcm=reverse:nwc=2.5:ptb=off:ssec=off:sio=off:spl=sat:updr=off_249");
	quick.push("ott+1_10_bs=off:bsr=unit_only:fsr=off:gsp=input_only:nwc=2.5:ptb=off:ssec=off_347");
	quick.push("dis+1011_7_bs=off:nwc=4:nicw=on:ptb=off:ssec=off:sos=all:sio=off:spo=on:spl=sat:ssfq=1.4:ssnc=none:updr=off_128");
	quick.push("dis+1011_64_bs=off:gs=on:nwc=3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=sat_141");
      }
      else {
	quick.push("dis+1011_64_bs=off:gs=on:nwc=3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=sat_4");
	quick.push("dis+2_3:2_bs=off:cond=on:lcm=reverse:nwc=1:nicw=on:ptb=off:ssec=off:sio=off:spl=sat_1");
	quick.push("ott+10_2:1_bs=off:bsr=on:cond=fast:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sp=occurrence:urr=on_25");
	quick.push("dis+1011_7_bs=off:cond=on:fsr=off:gs=on:nwc=1:ptb=off:ssec=off:sos=all:spl=sat_63");
	quick.push("ott+1_40_bsr=on:cond=fast:gs=on:nwc=1.5:ptb=off:ssec=off:sio=off:spo=on:spl=sat:urr=on_104");
	quick.push("ott+10_4_bs=off:gsp=input_only:gs=on:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:sp=occurrence:urr=on_107");
	quick.push("tab+10_1_spl=off:tfsr=off:tgawr=4/1:tglr=1/20:tipr=off:tlawr=8/1_112");
	quick.push("dis+1010_10_bs=off:nwc=1.1:ptb=off:ssec=off:sio=off_147");
	quick.push("dis-1002_4_bs=off:bsr=unit_only:gsp=input_only:gs=on:nwc=3:nicw=on:ptb=off:ssec=off:spl=sat:urr=on:updr=off_255");
	quick.push("ott-1010_128_bs=off:cond=on:nwc=1.3:ssec=off:urr=on_401");
      }
    }
    else {
      quick.push("ott+11_4_bs=off:nwc=1.2:nicw=on:ptb=off:sd=10:ss=axioms:st=2.0:sos=all:sac=on:sio=off:spo=on:spl=sat:ssfp=1000:ssfq=1.4:ssnc=none:updr=off_43");
      quick.push("ott-1010_1024_bs=off:drc=off:fde=none:nwc=2:sos=on_100");
      quick.push("dis+10_7_bd=off:bs=off:cond=fast:drc=off:ep=R:flr=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:sswn=on:sd=10:ss=included:st=1.5:spo=on:spl=backtracking_272");
      quick.push("tab+10_1_bms=on:sd=3:ss=axioms:st=1.2:sio=off:tbsr=off:tgawr=1/32:tglr=1/10:tipr=off:tlawr=3/1_47");
      quick.push("ott+11_14_bs=off:drc=off:ep=RS:flr=on:fde=none:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sio=off:spo=on_69");
      quick.push("dis-1002_2:3_bd=off:bs=off:cond=fast:drc=off:fde=none:nwc=3:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking_280");
      quick.push("dis+11_64_bs=off:cond=fast:gs=on:nwc=3:nicw=on:ptb=off:ss=axioms:st=1.2:sac=on:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none_88");
    }
    break;

  case Property::EPR:
    quick.push("ins+11_14_bs=off:flr=on:gsp=input_only:igbrr=0.7:igrr=1/8:igrp=4000:igrpq=1.5:igwr=on:lcm=predicate:nwc=3:ptb=off:ssec=off:spl=off:urr=on_55");
    quick.push("ott+10_8:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:spo=on:spl=sat:sser=off:ssnc=none:urr=on_166");
    quick.push("dis+1_8:1_bs=off:drc=off:flr=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.2_164");
    quick.push("ins+4_14_bs=off:cond=on:flr=on:igbrr=0.2:igrr=1/128:igrp=700:igrpq=1.2:igwr=on:nwc=1:ptb=off:ssec=off:spl=off:urr=on_41");
    quick.push("dis+1_20_bs=off:nwc=4:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat:ssfp=4000:ssfq=1.1:sp=occurrence:updr=off_285");
    quick.push("ott+1_24_bs=off:cond=fast:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:spo=on:spl=sat:urr=on_191");
    quick.push("ins+1_5_bs=off:bsr=on:drc=off:gs=on:igbrr=0.0:igrr=1/32:igrp=400:igrpq=2.0:igwr=on:lcm=predicate:nwc=2:ptb=off:ssec=off:sio=off:spl=off:sp=reverse_arity:urr=on:updr=off_264");
    quick.push("dis+3_10_bs=off:drc=off:ecs=on:fsr=off:nwc=1.2:nicw=on:ssec=off:sio=off:spl=off_477");
    break;
 
  case Property::UEQ:
    if (prop == 0) {
      if (atoms > 11) {
	quick.push("lrs+10_20_bs=off:drc=off:fsr=off:nwc=1:stl=120:sp=occurrence_295");
	quick.push("lrs+10_8:1_nwc=1:stl=90:sfv=off:sp=reverse_arity_271");
	quick.push("ott+10_7_bs=off:drc=off:fsr=off:nwc=1.1:sp=occurrence_249");
	quick.push("lrs+10_128_bs=unit_only:drc=off:fsr=off:nwc=1.2:stl=120:sfv=off:sp=occurrence_709");
	quick.push("dis+10_128_bs=unit_only:drc=off:fsr=off:gsp=input_only:nwc=10_296");
      }
      else {
	quick.push("lrs+10_20_bs=off:drc=off:fsr=off:nwc=1:stl=120:sp=occurrence_357");
	quick.push("ott+10_8:1_bs=off:drc=off:fsr=off:fde=none:nwc=5_372");
	quick.push("ott+10_7_bs=off:drc=off:fsr=off:gsp=input_only:nwc=3:sp=occurrence_504");
	quick.push("ott+10_1_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.3_527");
      }
    }
    else if (prop == 2) {
      if (atoms > 18) {
	quick.push("ott+10_8_bd=off:bs=off:drc=off:fsr=off:fde=none:nwc=2:sp=occurrence_45");
	quick.push("dis+10_5_bs=off:drc=off:fsr=off:nwc=1.5:sp=occurrence_386");
	quick.push("ott+10_3_bs=off:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.3:sp=occurrence_205");
	quick.push("lrs+10_128_bs=unit_only:drc=off:fsr=off:nwc=1.2:stl=120:sfv=off:sp=occurrence_1139");
      }
      else {
	quick.push("ott+10_6_bs=off:drc=off:fsr=off:fde=none:nwc=1.2_108");
	quick.push("ott+10_1_bs=off:drc=off:fsr=off:fde=none:nwc=5_2");
	quick.push("lrs+10_20_bd=off:bs=unit_only:drc=off:fsr=off:nwc=1.2:stl=90_528");
	quick.push("ott+10_32_bs=off:bsr=on:drc=off:fsr=off:fde=none:nwc=1.3_170");
	quick.push("ott+10_8:1_bs=off:bsr=on:nwc=1.3_113");
	quick.push("ott+10_3_bs=off:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.3:sp=occurrence_200");
	quick.push("ott+10_50_bd=off:drc=off:fsr=off:nwc=1.1:sp=occurrence_283");
      }
    }
    else {
      quick.push("dis+10_128_bs=unit_only:drc=off:fsr=off:gsp=input_only:nwc=10_148");
      quick.push("dis+4_5:1_bs=off:br=off:ep=RSTC:fsr=off:nwc=3:ptb=off:sos=all:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on_94");
      quick.push("lrs+10_128_bs=unit_only:drc=off:fsr=off:nwc=1.2:stl=120:sfv=off:sp=occurrence_610");
      quick.push("lrs+10_2:1_bd=off:bs=off:drc=off:fsr=off:nwc=2.5:stl=30_143");
    }
    break;
  }

  switch (cat) {
  case Property::NEQ:
    fallback.push("ott+1011_3_bs=off:bsr=unit_only:ep=on:nwc=2:ptb=off:ssec=off:spl=sat_300");
    fallback.push("dis-1002_2:1_bs=off:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:nicw=on:ptb=off:ssec=off:sos=all:sp=occurrence_300");
    fallback.push("ott+11_2_bd=off:bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=10:ptb=off:ssec=off:spl=sat:sp=reverse_arity_300");
    fallback.push("dis+11_5:1_bs=off:drc=off:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sos=all:sgo=on:sio=off:spo=on:spl=sat:sp=occurrence_300");
    fallback.push("dis+11_50_bs=off:drc=off:gsp=input_only:nwc=1.3:nicw=on:ptb=off:ssec=off:spl=sat:sser=off:ssfp=4000:ssfq=2.0:ssnc=none_300");
    fallback.push("dis+1011_24_cond=fast:drc=off:nwc=10:nicw=on:ptb=off:ssec=off:spl=sat_300");
    fallback.push("dis-1010_5_bs=off:bsr=unit_only:cond=fast:ep=on:gsp=input_only:lcm=reverse:nwc=1:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=backtracking:sp=occurrence_300");
    fallback.push("dis+10_14_bs=off:cond=fast:drc=off:gs=on:nwc=2.5:nicw=on:sd=1:ss=axioms:st=3.0:sac=on:spo=on:sp=occurrence_300");
    fallback.push("ott+1011_3_bs=off:drc=off:ep=on:fde=none:nwc=1.1:nicw=on:ptb=off:ssec=off:spl=sat_300");
    fallback.push("lrs+2_3:1_bs=off:br=off:drc=off:flr=on:lcm=predicate:nwc=10:ssec=off:sgo=on:sio=off:spo=on:sp=occurrence:urr=on_600");
    fallback.push("ott+11_5_bs=off:ep=on:fde=none:nwc=1.5:nicw=on:ptb=off:ssec=off:sswsr=on:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_300");
    fallback.push("dis+11_8:1_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sgo=on:sio=off:sp=occurrence_300");
    fallback.push("dis+11_8:1_bs=off:br=off:drc=off:ep=RST:nwc=1:ptb=off:ssec=off:sgo=on:sio=off:spo=on:spl=backtracking:urr=on_300");
    fallback.push("ott+11_8:1_drc=off:ep=on:nwc=1:ptb=off:ssec=off:sac=on:spo=on:sp=occurrence_600");
    fallback.push("dis+11_12_bs=off:drc=off:ep=on:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=3:nicw=on:ptb=off:ssec=off:sos=on:spl=sat_300");
    fallback.push("lrs+11_20_bd=off:bs=off:drc=off:gs=on:nwc=2.5:spo=on_600");
    fallback.push("ins-1010_8:1_bs=off:ep=RSTC:fsr=off:igbrr=1.0:igrr=1/128:igrp=200:igrpq=2.0:igwr=on:nwc=1.2:ptb=off:ssec=off:sos=on:sio=off:spl=off_300");
    fallback.push("dis+2_64_bs=off:cond=fast:drc=off:fsr=off:lcm=reverse:nwc=4:ptb=off:sos=on:spl=sat:sser=off:ssfp=100000:ssfq=1.4:ssnc=none_300");
    fallback.push("ott+3_8:1_bd=off:bs=off:bsr=unit_only:drc=off:fsr=off:nwc=1.2:nicw=on:ptb=off:ssec=off:sos=all:spl=sat:sser=off:ssfp=10000:ssfq=1.4:ssnc=none_300");
    fallback.push("ott+11_2:3_bd=off:bs=unit_only:bsr=unit_only:cond=on:drc=off:fde=none:lcm=reverse:nwc=1.2:ptb=off:ssec=off:spl=sat_300");
    fallback.push("ott-1010_3_bd=off:bs=off:cond=on:drc=off:ep=on:fde=none:nwc=10:ptb=off:ssec=off:sd=3:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sp=reverse_arity:urr=on_300");
    fallback.push("dis+1011_128_bs=unit_only:cond=fast:lcm=reverse:nwc=3:ptb=off:ssec=off:sos=on:spl=sat:sfv=off_300");
    fallback.push("ott-1002_2:1_bd=off:bs=off:bsr=on:drc=off:ep=on:flr=on:fsr=off:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:urr=on_300");
    fallback.push("ott+10_4:1_bd=off:bs=off:bsr=unit_only:drc=off:gsp=input_only:nwc=4:ptb=off:ssec=off:sos=all:sio=off:spo=on:urr=on:updr=off_300");
    fallback.push("ins+1011_3_bs=off:ep=RSTC:fde=none:gs=on:igbrr=1.0:igrr=1/64:igrp=100:igrpq=1.3:igwr=on:nwc=2.5:ptb=off:ssec=off:sos=on:sio=off:spl=off_300");
    fallback.push("ott+10_50_bs=off:br=off:cond=fast:drc=off:flr=on:gs=on:nwc=4:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:ssfq=2.0:ssnc=all:sp=reverse_arity:urr=on_300");
    fallback.push("ins-10_40_bs=off:cond=fast:ep=RSTC:flr=on:gsp=input_only:gs=on:igbrr=0.7:igrr=1/4:igrp=4000:igrpq=1.2:igwr=on:lcm=reverse:nwc=1.7:ptb=off:ssec=off:sio=off:spl=off:urr=on_300");
    fallback.push("dis-1010_3:2_bs=off:bsr=unit_only:drc=off:ep=RST:fde=none:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sos=on:sgo=on:spo=on:spl=backtracking:sp=reverse_arity_300");
    fallback.push("dis+11_50_bs=off:cond=fast:drc=off:fde=none:gs=on:lcm=predicate:nwc=2:nicw=on:ssec=off:spo=on:sp=reverse_arity_300");
    fallback.push("dis+10_1024_bs=off:cond=on:drc=off:flr=on:fsr=off:lcm=predicate:nwc=1.2:nicw=on:ptb=off:ssec=off:sac=on:spo=on_300");
    fallback.push("dis+11_24_bs=off:bms=on:cond=on:drc=off:ecs=on:fde=none:nwc=2.5:nicw=on:ssec=off:spo=on:sp=occurrence:urr=on_300");
    fallback.push("dis+11_5:1_bs=off:cond=fast:drc=off:nwc=10:sswn=on:sswsr=on_300");
    fallback.push("ott+10_2:3_bd=off:bs=off:cond=fast:drc=off:fde=none:lcm=predicate:nwc=10:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking:sp=occurrence_300");
    fallback.push("ott+10_28_bd=off:bs=off:drc=off:nwc=1.5:ptb=off:ssec=off:spl=sat_300");
    fallback.push("dis+1_5:1_bs=off:cond=on:drc=off:ep=RST:flr=on:fsr=off:lcm=reverse:nwc=10:ptb=off:ssec=off:sio=off:urr=on_300");
    fallback.push("ott-11_40_bd=off:bs=off:drc=off:ecs=on:flr=on:fsr=off:lcm=predicate:nwc=1.5:nicw=on:ssec=off:sos=on_300");
    fallback.push("ott+11_3_bs=off:br=off:drc=off:nwc=1.1:nicw=on:ss=axioms:sos=on:sio=off:urr=on_300");
    fallback.push("ott+1011_5_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:nwc=2:ptb=off:ssec=off:sos=on:sio=off:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1011_2_bs=off:cond=on:drc=off:ep=on:gsp=input_only:nwc=1.5:nicw=on:ptb=off:ssec=off:spl=sat:urr=on_300");
    fallback.push("dis+1011_2_bs=off:drc=off:ep=on:flr=on:nwc=1.1:nicw=on:ptb=off:ssec=off:spl=sat:urr=on:updr=off_300");
    fallback.push("dis+1011_64_bs=off:drc=off:ep=on:flr=on:nwc=2:ptb=off:ssec=off:spl=sat:sp=occurrence_300");
    fallback.push("dis+4_8:1_bs=off:bsr=on:drc=off:fsr=off:fde=none:lcm=reverse:nwc=10:ptb=off:ssec=off:spl=sat:ssfp=10000:ssfq=1.0:ssnc=none:sp=reverse_arity_300");
    fallback.push("dis-1010_3:1_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.7:nicw=on:ptb=off:spl=sat:sser=off:ssfp=100000:ssfq=1.1:ssnc=none_300");
    fallback.push("lrs+10_20_bd=off:bs=off:cond=fast:drc=off:ecs=on:nwc=1.5:ptb=off:ssec=off:sio=off:spo=on:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:updr=off_300");
    fallback.push("dis+11_5_bs=off:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking:sp=occurrence_300");
    fallback.push("ott+2_8:1_bd=off:bs=off:bsr=unit_only:bms=on:br=off:cond=fast:drc=off:nwc=1.5:ssec=off:sos=on:sio=off:urr=on:updr=off_100");
    fallback.push("ott+10_2_bd=off:bs=off:drc=off:ecs=on:flr=on:fsr=off:nwc=1.7:ssec=off:sac=on:sgo=on:sio=off_300");
    fallback.push("dis+11_4_ep=on:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:sos=on:spo=on:spl=sat_300");
    fallback.push("ott+2_3_bd=off:cond=on:drc=off:flr=on:nwc=1.3:ptb=off:ssec=off:sac=on:sgo=on:sio=off:sfv=off:sp=reverse_arity:updr=off_300");
    fallback.push("dis-1010_3_cond=fast:drc=off:nwc=4:sac=on_300");
    fallback.push("dis-2_50_bs=off:drc=off:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sio=off:spl=backtracking:sp=occurrence_300");
    fallback.push("dis+1011_7_bs=off:drc=off:ep=RS:fde=none:gsp=input_only:nwc=10:ptb=off:ssec=off:spl=sat:sser=off:ssfp=40000:ssfq=1.2:ssnc=none_300");
    fallback.push("dis+1011_16_bd=off:bs=off:cond=on:drc=off:ep=on:fsr=off:gs=on:nwc=2.5:ptb=off:ssec=off:sgo=on:spo=on:spl=backtracking_300");
    fallback.push("ott+11_50_bd=off:bs=off:drc=off:ep=on:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat:sp=occurrence_300");
    fallback.push("dis+1011_4:1_bs=off:bsr=on:drc=off:ep=on:flr=on:gsp=input_only:gs=on:lcm=reverse:nwc=2:ptb=off:ssec=off:sos=all:spo=on:spl=sat:ssfp=10000:ssnc=none:sp=occurrence_100");
    fallback.push("lrs-1002_4:1_bs=off:gs=on:nwc=4:nicw=on:ssec=off:sgo=on:spo=on:urr=on_600");
    fallback.push("ott+1011_6_bs=off:drc=off:ep=on:fde=none:nwc=1.1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat_300");
    fallback.push("ott+1011_6_drc=off:ep=on:fde=none:gs=on:nwc=1.3:nicw=on:ptb=off:ssec=off:sswsr=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off_300");
    fallback.push("ott+10_64_bd=off:bs=off:cond=fast:drc=off:flr=on:gsp=input_only:lcm=predicate:nwc=2:nicw=on:ptb=off:ssec=off:sac=on:spo=on_300");
    fallback.push("ott+1011_2:3_bd=off:bs=off:cond=fast:drc=off:ep=on:flr=on:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_300");
    fallback.push("dis-1010_7_bs=off:cond=fast:drc=off:fsr=off:gsp=input_only:gs=on:nwc=1.1:ptb=off:ssec=off:sio=off:spo=on:urr=on_300");
    fallback.push("dis+11_5:4_bs=off:bsr=on:cond=on:drc=off:fde=none:lcm=reverse:nwc=1.3:nicw=on:ptb=off:ssec=off:spl=sat:sscc=on:sser=off:ssfp=40000:ssfq=1.0_300");
    fallback.push("lrs+1011_20_bd=off:bs=off:ecs=on:ep=on:fde=none:lcm=predicate:nwc=3:nicw=on:ssec=off:sio=off:spl=off:urr=on_600");
    fallback.push("ott+2_40_bsr=unit_only:drc=off:fsr=off:fde=none:nwc=1:nicw=on:ptb=off:ssec=off:sio=off:urr=on_300");
    fallback.push("ott+1_10_bd=off:bs=off:drc=off:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sos=on:spl=sat_300");
    fallback.push("dis+10_5_bd=off:bs=off:cond=fast:ep=RST:gsp=input_only:lcm=predicate:nwc=5:ptb=off:ssec=off:sos=all:sac=on:sio=off:spl=backtracking:sfv=off:urr=on_100");
    fallback.push("dis+1011_12_bs=off:drc=off:fsr=off:nwc=5:nicw=on:ptb=off:ssec=off:sos=on:spl=sat_300");
    fallback.push("ott-11_8:1_bd=off:bs=off:drc=off:ep=on:fde=none:lcm=predicate:nwc=3:ptb=off:ssec=off:sos=on:sio=off:urr=on_300");
    break;

  case Property::HEQ:
  case Property::PEQ:
  case Property::EPR:
    fallback.push("dis+1_10_bs=off:fde=none:gsp=input_only:nwc=4:ptb=off:ssec=off:sac=on:sio=off:spl=sat_300");
    fallback.push("lrs+2_14_bs=off:cond=fast:drc=off:nwc=10:ptb=off:sac=on:sio=off:spo=on:spl=sat:ssac=none:ssfp=100000:ssfq=1.1:ssnc=all_dependent:sp=reverse_arity_900");
    fallback.push("ott+1_3_bs=off:bms=on:cond=on:drc=off:nwc=2:sac=on:sio=off:updr=off_900");
    fallback.push("ott+11_50_bs=off:cond=on:drc=off:flr=on:fde=none:lcm=predicate:nwc=2:nicw=on:ptb=off:sgo=on:sio=off:spl=backtracking:sp=occurrence:urr=on_1200");
    fallback.push("lrs-3_4_bsr=unit_only:cond=on:drc=off:fsr=off:fde=none:gs=on:nwc=1.2:ssec=off:sgo=on:sio=off:urr=on:updr=off_1500");
    fallback.push("ott+10_8:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:spo=on:spl=sat:sser=off:ssnc=none:urr=on_300");
    fallback.push("dis+1_6_bd=off:flr=on:gs=on:nwc=1.5:ptb=off:sos=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=2.0:ssnc=none:sp=reverse_arity_600");
    fallback.push("ins+11_14_bs=off:flr=on:gsp=input_only:igbrr=0.7:igrr=1/8:igrp=4000:igrpq=1.5:igwr=on:lcm=predicate:nwc=3:ptb=off:ssec=off:spl=off:urr=on_300");
    fallback.push("dis+2_128_bs=off:drc=off:lcm=predicate:nwc=10:sac=on:sio=off:sp=occurrence_300");
    fallback.push("dis+1_8:1_bs=off:drc=off:flr=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.2_300");
    fallback.push("dis+11_7_bs=off:drc=off:lcm=reverse:nwc=5:ssec=off:sio=off:spl=off:updr=off_600");
    fallback.push("dis+4_50_bd=off:bs=unit_only:cond=on:drc=off:gs=on:lcm=predicate:nwc=5:nicw=on:ptb=off:sos=all:sio=off:spl=backtracking:urr=on_500");
    fallback.push("ott+2_1024_bs=off:drc=off:gsp=input_only:nwc=1.1:ptb=off:ssec=off:spl=sat:ssfq=1.4:ssnc=none:sp=occurrence_600");
    fallback.push("ott+1_24_bs=off:cond=fast:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:spo=on:spl=sat:urr=on_300");
    fallback.push("dis+1_20_bs=off:nwc=4:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat:ssfp=4000:ssfq=1.1:sp=occurrence:updr=off_300");
    fallback.push("lrs+11_2:3_bd=off:drc=off:flr=on:nwc=1.3:nicw=on:ptb=off:sio=off:spl=sat:ssnc=none_900");
    fallback.push("dis+10_5:4_cond=on:gs=on:nwc=2:nicw=on:ptb=off:sos=all:sio=off:spl=sat:sscc=on:sser=off:ssfp=1000:ssfq=1.1:ssnc=none:sfv=off:sp=occurrence_600");
    fallback.push("dis+1_12_bs=off:drc=off:ep=on:nwc=1.3:nicw=on:sos=on:sio=off:spl=off_300");
    fallback.push("lrs+11_4:1_bs=unit_only:cond=fast:drc=off:fde=none:lcm=predicate:nwc=10:nicw=on:ptb=off:sac=on:spo=on:spl=sat:ssac=none:ssfp=1000:ssfq=1.0:ssnc=all_600");
    fallback.push("dis+2_8_bd=off:bs=off:ep=RST:fsr=off:lcm=reverse:nwc=3:nicw=on:ptb=off:ssec=off:spo=on:spl=backtracking:sfv=off_300");
    fallback.push("lrs+11_1_bd=off:bs=off:cond=on:drc=off:gs=on:nwc=2:ptb=off:spl=sat:sser=off:ssfp=1000:ssfq=1.0:ssnc=none_300");
    fallback.push("dis+10_10_bs=off:cond=fast:drc=off:fsr=off:nwc=1.2:nicw=on:ptb=off:sio=off:spo=on:spl=sat:sser=off:ssnc=none_600");
    fallback.push("ott+3_128_bs=off:br=off:cond=fast:drc=off:ep=on:nwc=1:nicw=on:ptb=off:sos=all:sio=off:spo=on:spl=backtracking:urr=on_300");
    fallback.push("ott+4_6_bs=off:bsr=on:cond=on:drc=off:fsr=off:nwc=3:ssec=off:sswn=on:sac=on:sio=off:sp=occurrence_300");
    fallback.push("ins+1_5_bs=off:bsr=on:drc=off:gs=on:igbrr=0.0:igrr=1/32:igrp=400:igrpq=2.0:igwr=on:lcm=predicate:nwc=2:ptb=off:ssec=off:sio=off:spl=off:sp=reverse_arity:urr=on:updr=off_300");
    fallback.push("dis-1010_3_bs=off:drc=off:lcm=predicate:nwc=10:ptb=off:ssec=off:spo=on_300");
    fallback.push("dis+1_2:1_bs=off:cond=on:drc=off:nwc=5:sos=on:sio=off:spo=on:sp=occurrence_300");
    fallback.push("ott+4_5_bd=off:bsr=unit_only:cond=fast:drc=off:fsr=off:gs=on:nwc=1.5:nicw=on:sac=on:sio=off_300");
    fallback.push("dis+11_8_bsr=unit_only:cond=on:drc=off:fsr=off:gs=on:nwc=1.1:nicw=on:ptb=off:ssec=off:sos=all:sio=off:spo=on:spl=sat:sser=off:ssfq=1.4:ssnc=none_200");
    fallback.push("ott+4_28_bs=off:cond=on:drc=off:fde=none:gs=on:nwc=1.1:ptb=off:ssec=off:sgo=on:sio=off:spo=on:spl=sat_300");
    fallback.push("ott+10_8:1_drc=off:ecs=on:ep=RSTC:gs=on:nwc=1.3:ssec=off:sac=on:sio=off_300");
    fallback.push("ott+3_20_bs=off:cond=fast:drc=off:fde=none:nwc=2:ptb=off:ssec=off:sgo=on:sio=off:spo=on:spl=sat:sp=occurrence_300");
    fallback.push("ins+4_14_bs=off:cond=on:flr=on:igbrr=0.2:igrr=1/128:igrp=700:igrpq=1.2:igwr=on:nwc=1:ptb=off:ssec=off:spl=off:urr=on_300");
    fallback.push("dis-1004_1024_bs=off:cond=fast:drc=off:ep=on:nwc=1.2_300");
    fallback.push("ins+4_3_cond=fast:flr=on:igbrr=0.6:igrr=1/128:igrp=700:igrpq=1.2:igwr=on:nwc=1.7:ptb=off:sio=off:spl=off:updr=off_300");
    fallback.push("ott+11_40_bd=off:bs=off:cond=on:drc=off:nwc=3:nicw=on:ptb=off:ssec=off:spl=sat:sp=reverse_arity_300");
    fallback.push("dis+3_10_bs=off:drc=off:ecs=on:fsr=off:nwc=1.2:nicw=on:ssec=off:sio=off:spl=off_600");
    fallback.push("ott+10_64_bs=off:cond=on:drc=off:ecs=on:flr=on:gsp=input_only:nwc=5:nicw=on:ssec=off:spo=on:sp=reverse_arity:updr=off_600");
    fallback.push("dis+2_6_bd=off:drc=off:flr=on:fsr=off:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_600");
    fallback.push("ott+11_64_bs=off:drc=off:ecs=on:gs=on:nwc=1.5:ssec=off:sio=off:spl=off_900");
    fallback.push("ins+11_50_bs=off:drc=off:fde=none:igbrr=0.7:igrr=1/32:igrp=700:igrpq=1.2:igwr=on:nwc=3:ptb=off:sio=off:spl=off:sp=reverse_arity_1200");
    break;

  case Property::HNE: 
  case Property::NNE: 
    fallback.push("ott+4_6_bs=off:bsr=unit_only:cond=fast:nwc=1.2:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat_300");
    fallback.push("dis+1011_64_bs=off:nwc=1.7:ptb=off:ssec=off:spl=sat_300");
    fallback.push("dis+1011_20_bs=off:fsr=off:nwc=2:sio=off:spl=off_300");
    fallback.push("lrs+1002_7_bs=off:cond=on:flr=on:fsr=off:gsp=input_only:gs=on:lcm=predicate:nwc=1.2:ptb=off:spl=sat:sser=off:ssfp=40000:ssfq=2.0:ssnc=none_300");
    fallback.push("dis+4_12_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=10:ptb=off:ssec=off:spl=sat:sp=occurrence_300");
    fallback.push("lrs+10_3:1_bs=off:bsr=unit_only:cond=fast:nwc=10:ptb=off:ssec=off:sio=off:spo=on_900");
    fallback.push("dis+1011_128_bs=off:nwc=5:ptb=off:ssec=off:sswsr=on:sos=on:spl=sat_300");
    fallback.push("lrs-1003_28_bs=unit_only:bms=on:cond=on:flr=on:fsr=off:gsp=input_only:nwc=1:nicw=on:ssec=off:sio=off:spl=off:sp=occurrence_600");
    fallback.push("lrs+1_1024_bs=off:bms=on:cond=on:ecs=on:nwc=1:nicw=on:ssec=off:sac=on:sio=off_900");
    fallback.push("dis+11_128_bs=off:cond=fast:flr=on:lcm=reverse:nwc=2:ptb=off:ssec=off:spl=sat_300");
    fallback.push("dis+1011_20_bs=off:gsp=input_only:nwc=1.3:nicw=on:ptb=off:ssec=off:sswsr=on:sos=on:sac=on:sio=off:spo=on:spl=sat_300");
    fallback.push("dis-2_14_bs=off:cond=fast:flr=on:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spl=backtracking_300");
    fallback.push("lrs+3_8_bs=unit_only:cond=fast:flr=on:nwc=4:nicw=on:ptb=off:ssec=off:sio=off:spl=backtracking_300");
    fallback.push("dis+2_5:4_cond=fast:ecs=on:flr=on:nwc=1.5:ssec=off:sio=off:spl=off_600");
    fallback.push("dis+11_64_bs=unit_only:bms=on:lcm=reverse:nwc=1.5:sio=off_300");
    fallback.push("dis+1011_128_bs=off:cond=fast:flr=on:fsr=off:lcm=reverse:nwc=2.5:nicw=on:ptb=off:ssec=off:sswsr=on:spl=sat_300");
    fallback.push("dis+1011_6_bs=off:nwc=1.2:ptb=off:ssec=off:spl=sat_300");
    fallback.push("lrs+2_5:1_bs=off:cond=fast:flr=on:fsr=off:lcm=predicate:nwc=10:ptb=off:ssec=off:spl=backtracking_900");
    fallback.push("dis+11_20_bs=off:fsr=off:gsp=input_only:lcm=reverse:nwc=1.3:ptb=off:ssec=off:spl=sat:sp=occurrence_300");
    fallback.push("dis+11_1_bs=off:cond=fast:fsr=off:nwc=10:ptb=off:ssec=off:sio=off:spo=on:spl=sat_300");
    fallback.push("lrs+4_1024_bs=off:flr=on:fsr=off:gs=on:lcm=reverse:nwc=1.2:nicw=on:ptb=off:ssec=off:sos=on:sio=off:spo=on:spl=backtracking_300");
    fallback.push("dis+1_40_bs=off:cond=on:gsp=input_only:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:sgo=on:sio=off:spl=sat_300");
    fallback.push("dis+1011_12_bs=off:cond=fast:ecs=on:flr=on:nwc=1:ssec=off_300");
    fallback.push("dis+3_50_bs=off:fsr=off:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sos=on:spl=sat:updr=off_300");
    fallback.push("ott-1002_2_bs=off:ecs=on:flr=on:lcm=predicate:nwc=2:nicw=on:ssec=off:sos=on:spo=on:sp=reverse_arity:updr=off_300");
    fallback.push("dis+1_2:1_bs=off:bsr=unit_only:fsr=off:lcm=reverse:nwc=1.1:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:sser=off:ssfq=2.0_300");
    fallback.push("ott+1_8:1_bs=off:br=off:cond=on:gs=on:nwc=3:ptb=off:ssec=off:sio=off:spl=sat:urr=on_300");
    fallback.push("ott+1010_2_bs=off:gs=on:nwc=5:ptb=off:ssec=off:spl=sat_300");
    fallback.push("dis+1002_50_bs=off:fsr=off:lcm=predicate:nwc=1.2:nicw=on:ssec=off_600");
    fallback.push("lrs+1011_64_bs=unit_only:bsr=unit_only:cond=fast:flr=on:nwc=1:ptb=off:sio=off:spo=on:spl=backtracking_1800");
    break;

  case Property::FEQ: 
    fallback.push("dis+1011_14_bd=off:bs=off:drc=off:nwc=4:ptb=off:ssec=off:sswn=on:sac=on:spl=sat:sp=occurrence_300");
    fallback.push("ott+1011_8:1_bs=off:bsr=unit_only:drc=off:ep=on:fde=none:nwc=1.3:ptb=off:sd=2:ss=axioms:sos=all:spl=sat:sser=off:ssfq=1.0:ssnc=none:sfv=off_300");
    fallback.push("dis+1010_24_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=2.5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_300");
    fallback.push("ott+1_2_bs=off:bsr=unit_only:drc=off:lcm=predicate:nwc=4:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:spl=sat_300");
    fallback.push("dis+1_16_bd=off:bs=off:cond=fast:drc=off:fsr=off:nwc=1.2:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:urr=on_300");
    fallback.push("lrs+4_20_cond=fast:drc=off:flr=on:lcm=predicate:nwc=1.2:nicw=on:ptb=off:ssec=off:sgo=on:sio=off:spl=backtracking:sp=occurrence_900");
    fallback.push("ott-1002_5:4_bs=off:drc=off:fde=none:nwc=1.7:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:spl=sat:urr=on_300");
    fallback.push("dis+1_5:1_bs=off:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sagn=off:spl=sat:ssfq=1.4:ssnc=none_300");
    fallback.push("dis-1002_3_bs=off:cond=fast:drc=off:ep=RS:nwc=1.1:ptb=off:ssec=off:swb=on_300");
    fallback.push("dis+2_24_bs=off:ep=RSTC:flr=on:lcm=reverse:nwc=5:nicw=on:ssec=off:sac=on:sgo=on:spo=on:sfv=off_1200");
    fallback.push("dis+1011_3_bs=off:drc=off:fde=none:gs=on:nwc=1.1:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sio=off:spl=sat_300");
    fallback.push("dis+2_8:1_bd=off:bs=off:bsr=unit_only:drc=off:lcm=reverse:nwc=2.5:nicw=on:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=5:ss=axioms:st=1.5:sos=on:spl=sat:sp=reverse_arity_300");
    fallback.push("ott+1010_2:3_bs=off:drc=off:fde=none:nwc=1.2:sac=on_300");
    fallback.push("dis+11_8:1_bs=off:br=off:cond=on:drc=off:ecs=on:ep=RST:fsr=off:nwc=1:ptb=off:ssec=off:sd=7:ss=axioms:st=2.0:sio=off:spo=on:spl=sat:ssnc=none:urr=on:updr=off_300");
    fallback.push("dis-1010_5:1_bsr=on:drc=off:fde=none:gsp=input_only:gs=on:nwc=4:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:updr=off_300");
    fallback.push("dis+1_2_bs=off:cond=on:drc=off:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=2.0:sagn=off:sac=on:sio=off:spl=sat:sser=off:ssnc=none:updr=off_300");
    fallback.push("ott+1011_10_bd=off:bs=off:drc=off:ep=on:fde=none:gs=on:nwc=5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_300");
    fallback.push("ins+1011_3:1_bs=off:cond=fast:ep=RSTC:igbrr=0.8:igrr=1/2:igrp=200:igrpq=1.0:igwr=on:nwc=2:ptb=off:ssec=off:sos=all:sio=off:spl=off_300");
    fallback.push("lrs+3_8:1_bsr=on:cond=on:drc=off:flr=on:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sgo=on:sio=off:spl=backtracking:sp=reverse_arity:urr=on_900");
    fallback.push("ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:spl=backtracking_300");
    fallback.push("ins-11_8:1_bs=off:bsr=unit_only:igbrr=0.9:igrr=1/128:igrp=400:igrpq=1.5:igwr=on:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sos=all:spl=off:sp=occurrence:updr=off_300");
    fallback.push("ott+2_6_bs=off:cond=fast:drc=off:fde=none:nwc=1.2:ptb=off:ssec=off:sio=off:spl=sat_300");
    fallback.push("dis-1_1_bs=off:ep=RSTC:gs=on:nwc=1.1:sd=1:ss=included:st=5.0:sos=on:sio=off:sfv=off_300");
    fallback.push("dis+10_5:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spl=sat:sp=reverse_arity_300");
    fallback.push("ott+1_12_bs=off:br=off:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat:sser=off:ssfq=1.0:ssnc=none:urr=on_300");
    fallback.push("dis-1010_7_bs=off:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:updr=off_300");
    fallback.push("dis-1010_3_bs=off:drc=off:fde=none:nwc=1:nicw=on:ptb=off:ssec=off:sd=1:ss=axioms:st=3.0:sac=on:sio=off:spl=sat_300");
    fallback.push("dis-2_4:1_bs=off:drc=off:ep=on:lcm=predicate:nwc=3:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:spl=sat:sp=occurrence:updr=off_300");
    fallback.push("ott-1002_1024_bd=off:bs=off:cond=on:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sos=on:sgo=on:sio=off:spo=on:spl=backtracking:urr=on_300");
    fallback.push("ott+2_5:1_bd=off:bs=off:drc=off:gsp=input_only:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:sos=on:spl=sat:urr=on_300");
    fallback.push("lrs+1003_8:1_bs=off:drc=off:ep=on:fsr=off:gsp=input_only:gs=on:nwc=1.5:ptb=off:ssec=off:sio=off:spl=sat_300");
    fallback.push("ott+4_3:1_bs=off:bms=on:br=off:drc=off:fde=none:nwc=1.7:nicw=on:sd=3:ss=axioms:st=3.0:sos=all:sio=off:spl=off:sfv=off:urr=on_300");
    fallback.push("dis+2_5:4_bs=off:br=off:cond=on:drc=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sio=off:spl=backtracking:urr=on_300");
    fallback.push("lrs+11_2:1_bs=off:cond=on:drc=off:ep=on:fde=none:gs=on:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sio=off:spo=on:spl=backtracking:urr=on_300");
    fallback.push("ott-11_4:1_bs=off:bsr=on:cond=fast:drc=off:ecs=on:nwc=1.3:ssec=off:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sio=off_300");
    fallback.push("dis+2_4_bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:nicw=on:ptb=off:ssec=off:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sgo=on:spl=backtracking:sp=reverse_arity_300");
    fallback.push("dis-1010_2_bs=off:cond=fast:drc=off:nwc=1.7:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sio=off:spl=backtracking:updr=off_300");
    fallback.push("dis+1_3:1_bs=off:cond=fast:drc=off:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sswn=on:sd=1:ss=included:st=1.5:sos=on:sagn=off:sac=on:sio=off:spl=backtracking:sp=occurrence_300");
    fallback.push("lrs+3_24_bd=off:cond=on:drc=off:nwc=1.3:ptb=off:ssec=off:sio=off:spl=sat:sp=occurrence_300");
    fallback.push("dis-1004_3:2_bs=off:cond=fast:drc=off:ep=RST:gsp=input_only:nwc=5:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:st=1.2:sos=on:spl=sat_300");
    fallback.push("dis+1011_3_bd=off:bs=off:drc=off:ep=on:fde=none:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_300");
    fallback.push("dis+1010_128_bs=off:cond=fast:drc=off:ep=on:flr=on:gs=on:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sswsr=on:sd=3:ss=axioms:st=1.5:sos=on:sagn=off:sac=on:sio=off:spo=on:spl=sat:sfv=off_300");
    fallback.push("ott+1_8_bs=off:drc=off:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_300");
    fallback.push("dis+11_2:1_bs=off:cond=fast:drc=off:fde=none:gs=on:nwc=2:nicw=on:ptb=off:ssec=off:sos=all:sac=on:sio=off:spo=on:spl=sat:sscc=on:sser=off:ssfq=2.0:sp=occurrence_100");
    fallback.push("dis-1010_7_bs=off:cond=fast:drc=off:fde=none:nwc=2:ptb=off:ssec=off:spo=on:sp=occurrence_300");
    fallback.push("dis+3_2_bs=off:drc=off:ep=RST:fsr=off:nwc=1:ptb=off:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:spl=sat:ssfq=2.0:ssnc=none:sfv=off_300");
    fallback.push("ott+11_64_bd=off:bs=off:br=off:cond=fast:drc=off:ep=on:gsp=input_only:gs=on:nwc=2:ptb=off:ssec=off:sos=all:sio=off:spl=backtracking:urr=on_100");
    fallback.push("ott+1011_1_bs=off:cond=on:drc=off:ecs=on:nwc=2:nicw=on:ptb=off:ssec=off:spl=sat:ssfp=1000:ssfq=1.2:ssnc=none_300");
    fallback.push("ott-1_2:3_bs=off:bms=on:cond=on:drc=off:fde=none:lcm=predicate:nwc=1.7:nicw=on:sd=5:ss=axioms:st=1.2:sio=off:urr=on_300");
    fallback.push("dis-1010_5:4_bs=off:bms=on:drc=off:nwc=10:sd=2:ss=axioms:st=1.5:sac=on:sio=off:updr=off_300");
    fallback.push("ott+2_8_bd=off:bs=off:bsr=unit_only:cond=on:flr=on:nwc=2:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:updr=off_300");
    fallback.push("lrs-1004_50_bs=off:br=off:cond=fast:drc=off:nwc=1.5:nicw=on:sio=off:spl=off:urr=on:updr=off_600");
    fallback.push("ott+1_50_bd=off:bs=unit_only:drc=off:nwc=1.1:nicw=on:ptb=off:sio=off:spl=sat:ssfp=10000:ssfq=1.0:ssnc=all_dependent:sp=reverse_arity_300");
    fallback.push("ott+1_10_bs=off:cond=fast:drc=off:flr=on:lcm=predicate:nwc=10:ptb=off:ssec=off:sac=on:sio=off:spo=on:sp=occurrence:urr=on_300");
    fallback.push("ott-1003_2:1_bs=unit_only:bsr=unit_only:drc=off:nwc=1.2:ptb=off:ssec=off:sio=off:updr=off_300");
    fallback.push("ott-1010_8:1_bs=off:flr=on:fsr=off:gs=on:nwc=4:ptb=off:ssec=off:sac=on:sio=off:sp=reverse_arity:urr=on_600");
    fallback.push("dis+11_2:1_bs=off:ep=on:nwc=1:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:spl=sat_300");
    fallback.push("ott+3_32_bd=off:bs=off:drc=off:flr=on:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:spl=sat:updr=off_300");
    fallback.push("ott+11_8:1_bs=off:drc=off:ecs=on:fsr=off:gs=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:sos=all:spl=sat:ssfq=2.0:ssnc=none_300");
    fallback.push("dis+2_1_bs=off:bsr=unit_only:drc=off:fsr=off:gsp=input_only:gs=on:lcm=reverse:nwc=5:ptb=off:ssec=off:sswn=on:sd=2:sgt=7:ss=axioms:st=1.2:sos=on:sio=off:spl=sat_300");
    fallback.push("dis+2_5:1_bd=off:bs=off:ep=RSTC:gs=on:lcm=reverse:nwc=1.2:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:sac=on:sio=off:sfv=off:sp=reverse_arity_300");
    fallback.push("dis+10_8:1_bs=off:br=off:cond=on:drc=off:ecs=on:ep=RST:fsr=off:nwc=1.7:ptb=off:ssec=off:sd=4:ss=axioms:st=3.0:spo=on:spl=sat:ssfq=2.0:ssnc=none:urr=on_300");
    fallback.push("dis+1_14_bs=off:br=off:drc=off:fde=none:gs=on:nwc=1.1:ssec=off:sd=2:ss=axioms:st=2.0:sac=on:sio=off:urr=on_300");
    fallback.push("dis+1011_12_bs=off:cond=fast:drc=off:ep=RS:flr=on:nwc=1.5:ptb=off:ssec=off:spl=sat_300");
    fallback.push("lrs+1_20_bs=off:cond=fast:gs=on:nwc=4:ptb=off:ssec=off:sswsr=on:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sio=off:spo=on:spl=backtracking:updr=off_300");
    fallback.push("dis+11_4:1_bs=off:drc=off:ep=RST:fde=none:lcm=reverse:nwc=5:nicw=on:ssec=off:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sgo=on:sio=off:sp=occurrence_300");
    fallback.push("dis+2_4_bs=off:drc=off:ep=RST:flr=on:lcm=reverse:nwc=1.7:ptb=off:ssec=off:sos=on:spl=sat:sp=reverse_arity_300");
    fallback.push("ott+2_8:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ecs=on:ep=RST:flr=on:fde=none:lcm=reverse:nwc=5:ssec=off:sac=on:sio=off:urr=on_300");
    fallback.push("dis+10_16_bs=off:cond=fast:drc=off:ecs=on:gsp=input_only:nwc=10:nicw=on:ssec=off:sos=on:sac=on:urr=on_100");
    fallback.push("dis+1011_2_bs=off:cond=on:drc=off:gs=on:nwc=4:ptb=off:ssec=off:sd=1:ss=axioms:st=1.2:spl=sat:updr=off_300");
    fallback.push("ott-1004_3:2_br=off:drc=off:fsr=off:nwc=1.5:nicw=on:ptb=off:ssec=off:sos=all:spl=sat:ssfp=100000:ssfq=1.2:ssnc=none:urr=on_200");
    fallback.push("ott+3_16_bd=off:bs=off:bsr=unit_only:nwc=4:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:sser=off:ssfp=100000:ssfq=1.2_300");
    fallback.push("ott+1_4_bs=off:cond=on:drc=off:ep=on:flr=on:nwc=4:nicw=on:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:sos=on:sagn=off:spl=sat_300");
    fallback.push("dis-1002_1024_bs=off:bms=on:cond=fast:drc=off:ecs=on:ep=on:lcm=predicate:nwc=3:nicw=on:ssec=off:sswn=on:sswsr=on:sac=on_300");
    fallback.push("dis+1_4_bs=off:drc=off:ep=on:fde=none:lcm=reverse:nwc=5:ptb=off:ssec=off:sos=on:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none:sp=reverse_arity_300");
    fallback.push("dis+1_2:1_bd=off:bs=off:bsr=on:drc=off:ep=on:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sio=off:spo=on:spl=backtracking_300");
    fallback.push("ott+10_64_bd=off:bs=off:cond=on:drc=off:ecs=on:gs=on:nwc=1:ssec=off:sac=on:sio=off_300");
    fallback.push("ott+3_28_bs=off:drc=off:fde=none:nwc=1.3:nicw=on:sac=on:sio=off_300");
    fallback.push("dis+1002_5:1_bs=off:bms=on:drc=off:ep=on:flr=on:fde=none:gsp=input_only:nwc=1:nicw=on:ssec=off:sac=on:sio=off:updr=off_600");
    fallback.push("ott+10_1024_bs=off:drc=off:nwc=1.7:ssec=off:sac=on:sio=off:sp=occurrence:updr=off_600");
    fallback.push("dis-1010_40_bs=off:cond=on:drc=off:gs=on:nwc=3:nicw=on:ptb=off:ssec=off:sd=4:ss=axioms:st=1.5:sos=on:sio=off:spl=sat_300");
    fallback.push("ott+11_50_bd=off:bs=off:cond=fast:drc=off:ep=on:fsr=off:lcm=reverse:nwc=1:nicw=on:ptb=off:ssec=off:sos=on:spl=backtracking:sp=occurrence:updr=off_300");
    fallback.push("ott-11_8:1_bd=off:bs=off:drc=off:lcm=reverse:nwc=3:sio=off:spl=off:urr=on_300");
    fallback.push("ott+2_8:1_bs=off:bsr=on:cond=fast:drc=off:fde=none:lcm=reverse:nwc=4:nicw=on:ptb=off:ssec=off:sos=on:spl=sat:sser=off:ssfp=100000:ssnc=none:urr=on_300");
    fallback.push("dis+1011_2_bs=off:cond=fast:drc=off:fde=none:gs=on:nwc=4:ptb=off:ssec=off:sio=off:spl=backtracking:sp=occurrence_300");
    fallback.push("dis-1010_1024_bs=off:cond=fast:drc=off:fde=none:lcm=reverse:nwc=4:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=sat_300");
    fallback.push("ott+10_3:1_bsr=unit_only:cond=on:fsr=off:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat:urr=on:updr=off_300");
    fallback.push("lrs+1_4_bs=off:drc=off:ecs=on:ep=on:flr=on:fsr=off:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:spl=sat:sser=off:ssfp=40000:ssfq=1.1:ssnc=none:sp=occurrence_300");
    fallback.push("dis-1010_128_bs=off:ep=RST:nwc=5:ptb=off:sd=1:ss=included:st=2.0:sos=on:sac=on:sio=off:spl=sat:sser=off:ssfq=1.2:ssnc=none:sfv=off_300");
    fallback.push("ott+1_5:1_bs=off:br=off:cond=fast:drc=off:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=5.0:sos=all:sio=off:spl=sat:urr=on_300");
    fallback.push("dis+1_2:1_bs=off:bms=on:br=off:drc=off:gsp=input_only:gs=on:lcm=predicate:nwc=1:nicw=on:ssec=off:sd=3:sgt=7:ss=axioms:st=2.0:sos=on:spo=on:urr=on_300");
    fallback.push("dis+11_1_bs=off:bms=on:drc=off:ep=RS:flr=on:fde=none:nwc=5:sos=on:sgo=on:sio=off_300");
    fallback.push("dis+1010_7_bs=off:bsr=on:bms=on:drc=off:fsr=off:fde=none:gs=on:nwc=1.7:sac=on:sgo=on:sio=off:sp=occurrence_300");
    fallback.push("dis+1011_64_bs=off:drc=off:fde=none:lcm=predicate:nwc=5:nicw=on:ssec=off:sswn=on:sp=reverse_arity_300");
    fallback.push("dis+10_128_bd=off:bs=off:drc=off:nwc=3:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking_300");
    fallback.push("ott+11_8:1_bd=off:bs=unit_only:bsr=unit_only:drc=off:fsr=off:lcm=reverse:nwc=1.1:nicw=on:ptb=off:ssec=off:spl=sat:ssfq=2.0:ssnc=none_300");
    fallback.push("ott+11_2:1_bs=off:cond=fast:drc=off:ep=RS:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=2.5:ptb=off:ssec=off:spl=sat:sp=occurrence_300");
    fallback.push("dis+1_3:1_bs=off:drc=off:fde=none:gs=on:nwc=1.7:ptb=off:ssec=off:sos=all:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence_100");
    fallback.push("dis-4_3:2_cond=on:drc=off:gs=on:nwc=4:nicw=on:ptb=off:sio=off:spl=sat:sser=off:ssfp=1000:ssfq=2.0:ssnc=none:sp=occurrence_300");
    fallback.push("ott-4_7_bs=off:drc=off:fde=none:gs=on:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=backtracking:urr=on_300");
    fallback.push("dis+10_64_bd=off:bs=off:cond=fast:drc=off:ep=RSTC:flr=on:gsp=input_only:nwc=4:nicw=on:ptb=off:ssec=off:sswn=on:sd=10:ss=included:st=2.0:sos=all:spl=backtracking_300");
    fallback.push("dis+1011_5:1_bs=off:cond=fast:drc=off:ep=RS:nwc=5:nicw=on:ptb=off:ssec=off:sio=off:spo=on_200");
    fallback.push("ott+1_8:1_bs=off:drc=off:ep=on:flr=on:gsp=input_only:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spl=backtracking_300");
    fallback.push("ott+11_2:3_bs=off:cond=on:drc=off:flr=on:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:spo=on:spl=sat:sp=reverse_arity:urr=on_300");
    fallback.push("ott+1011_5:1_bs=off:cond=fast:drc=off:nwc=2.5:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=backtracking:sp=occurrence_300");
    fallback.push("lrs-3_10_drc=off:nwc=5:ptb=off:ssec=off:spl=sat:sser=off:ssfp=4000:ssnc=none:urr=on_300");
    fallback.push("ott-2_5:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking_300");
    fallback.push("dis+2_12_drc=off:ep=RST:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:spl=sat:sp=occurrence_300");
    fallback.push("dis+10_64_bs=off:cond=on:drc=off:ep=RS:nwc=1:ptb=off:ssec=off:sio=off:spo=on_300");
    fallback.push("ott-1010_4_bs=off:cond=fast:drc=off:fsr=off:gs=on:nwc=10:nicw=on:ptb=off:ssec=off:sd=4:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spl=backtracking:sfv=off_300");
    fallback.push("dis+2_128_bs=off:bms=on:drc=off:fde=none:lcm=reverse:nwc=1.3:nicw=on:ssec=off:sos=on:sio=off:spl=off_300");
    fallback.push("dis+3_4_bd=off:bs=off:cond=fast:drc=off:fsr=off:fde=none:gs=on:lcm=reverse:nwc=1.7:ptb=off:ssec=off:sos=on:spl=sat_300");
    fallback.push("lrs+11_50_bs=off:bms=on:cond=fast:drc=off:ecs=on:nwc=1.1:ssec=off:urr=on_900");
    fallback.push("dis+2_8:1_bs=off:drc=off:flr=on:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:spl=sat_300");
    fallback.push("ins+10_4:1_bs=off:bsr=unit_only:cond=on:ep=RSTC:gs=on:igbrr=0.4:igrr=1/128:igrp=100:igrpq=1.3:igwr=on:nwc=1.1:ptb=off:ssec=off:sos=on:sio=off:spl=off:urr=on_300");
    fallback.push("dis+11_16_bs=off:drc=off:gs=on:nwc=5:nicw=on:ptb=off:ssec=off:sos=on:sio=off:spo=on:spl=sat:sser=off:ssfp=1000:ssnc=none:sp=occurrence:urr=on_300");
    fallback.push("dis-1_6_bs=off:bsr=unit_only:cond=on:drc=off:fsr=off:gs=on:lcm=predicate:nwc=1.1:ptb=off:ssec=off:sos=on:sio=off:spo=on:urr=on_300");
    fallback.push("ott+4_5:1_bd=off:bs=off:cond=fast:drc=off:fde=none:gsp=input_only:nwc=3:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:urr=on_300");
    fallback.push("ins-1003_3_bs=off:ep=RSTC:flr=on:gsp=input_only:igbrr=0.0:igrr=1/128:igrp=1400:igrpq=2.0:igwr=on:nwc=2:ptb=off:ssec=off:sos=on:sio=off:spl=off_300");
    fallback.push("ott+11_10_bd=off:bs=off:cond=fast:drc=off:lcm=predicate:nwc=1:nicw=on:sac=on:sgo=on:urr=on_600");
    fallback.push("ott+3_3_bs=off:bsr=unit_only:cond=fast:drc=off:fsr=off:fde=none:gs=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sgo=on:spo=on:spl=backtracking:sp=occurrence_600");
    fallback.push("lrs-2_2:1_bs=off:br=off:cond=on:ep=on:fde=none:lcm=reverse:nwc=10:ptb=off:ssec=off:sos=on:sio=off:spo=on:urr=on_600");
    fallback.push("ott+11_12_cond=fast:drc=off:ecs=on:gs=on:nwc=1.2:nicw=on:ssec=off:sp=occurrence_600");
    fallback.push("ott+3_24_bs=unit_only:drc=off:ecs=on:fde=none:nwc=1.1:ssec=off:sos=all:sac=on_600");
    fallback.push("ott+1_5:1_bs=off:cond=fast:drc=off:fde=none:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:sos=on:spl=sat:sp=occurrence_300");
    break;

  case Property::FNE:
    fallback.push("dis-1002_2:3_bd=off:bs=off:cond=fast:drc=off:fde=none:nwc=3:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking_300");
    fallback.push("dis-1002_4_bs=off:bsr=unit_only:gsp=input_only:gs=on:nwc=3:nicw=on:ptb=off:ssec=off:spl=sat:urr=on:updr=off_300");
    fallback.push("dis+11_64_bs=off:cond=fast:gs=on:nwc=3:nicw=on:ptb=off:ss=axioms:st=1.2:sac=on:spl=sat:sser=off:ssfp=1000:ssfq=1.2:ssnc=none_100");
    fallback.push("dis+11_40_bs=off:bsr=on:cond=on:fsr=off:lcm=reverse:nwc=2.5:ptb=off:ssec=off:sio=off:spl=sat:updr=off_300");
    fallback.push("ins+1011_128_bs=off:cond=fast:gs=on:igbrr=0.3:igrr=1/64:igrpq=1.3:igwr=on:nwc=5:ptb=off:sos=all:sio=off:spl=off_300");
    fallback.push("dis+10_7_bd=off:bs=off:cond=fast:drc=off:ep=R:flr=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:sswn=on:sd=10:ss=included:st=1.5:spo=on:spl=backtracking_300");
    fallback.push("dis+1011_64_bs=off:gs=on:nwc=3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spl=sat_300");
    fallback.push("dis+3_7_bs=off:bms=on:cond=fast:ecs=on:fsr=off:lcm=reverse:nwc=1.1:ssec=off_300");
    fallback.push("ott-1010_1024_bs=off:drc=off:fde=none:nwc=2:sos=on_300");
    fallback.push("ott+10_2:1_bs=off:bsr=on:cond=fast:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sp=occurrence:urr=on_300");
    fallback.push("dis+1004_6_bs=off:nwc=4:nicw=on:ptb=off:ssec=off:sagn=off:spl=backtracking_300");
    fallback.push("ott+1_10_bs=off:bsr=unit_only:fsr=off:gsp=input_only:nwc=2.5:ptb=off:ssec=off_600");
    fallback.push("tab+10_1_bms=on:sd=3:ss=axioms:st=1.2:sio=off:tbsr=off:tgawr=1/32:tglr=1/10:tipr=off:tlawr=3/1_100");
    fallback.push("ott+1_40_bsr=on:cond=fast:gs=on:nwc=1.5:ptb=off:ssec=off:sio=off:spo=on:spl=sat:urr=on_300");
    fallback.push("ott+10_4_bs=off:gsp=input_only:gs=on:lcm=reverse:nwc=10:nicw=on:ptb=off:ssec=off:sp=occurrence:urr=on_300");
    fallback.push("ott+11_14_bs=off:drc=off:ep=RS:flr=on:fde=none:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sio=off:spo=on_300");
    fallback.push("dis+1010_10_bs=off:nwc=1.1:ptb=off:ssec=off:sio=off_300");
    fallback.push("dis+1011_7_bs=off:nwc=4:nicw=on:ptb=off:ssec=off:sos=all:sio=off:spo=on:spl=sat:ssfq=1.4:ssnc=none:updr=off_300");
    fallback.push("tab+10_1_spl=off:tfsr=off:tgawr=4/1:tglr=1/20:tipr=off:tlawr=8/1_300");
    fallback.push("dis+1011_7_bs=off:cond=on:fsr=off:gs=on:nwc=1:ptb=off:ssec=off:sos=all:spl=sat_300");
    fallback.push("ott-1010_128_bs=off:cond=on:nwc=1.3:ssec=off:urr=on_600");
    break;

  case Property::UEQ:
    fallback.push("lrs+11_20_bs=off:drc=off:ep=on:flr=on:gs=on:nwc=4:sp=occurrence_1200");
    fallback.push("ott+10_6_bs=off:drc=off:fsr=off:fde=none:nwc=1.2_300");
    fallback.push("lrs+10_128_bs=unit_only:drc=off:fsr=off:nwc=1.2:sfv=off:sp=occurrence_1200");
    fallback.push("dis+4_5:1_bs=off:br=off:ep=RSTC:fsr=off:nwc=3:ptb=off:sos=all:sio=off:spl=sat:ssfq=1.4:ssnc=none:urr=on_300");
    fallback.push("ott+10_8:1_bs=off:drc=off:fsr=off:fde=none:nwc=5_600");
    fallback.push("ott+10_7_bs=off:drc=off:fsr=off:gsp=input_only:nwc=3:sp=occurrence_600");
    fallback.push("lrs+10_20_bd=off:bs=unit_only:drc=off:fsr=off:nwc=1.2_900");
    fallback.push("ott+10_3_bs=off:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.3:sp=occurrence_300");
    fallback.push("ott+10_32_bs=off:bsr=on:drc=off:fsr=off:fde=none:nwc=1.3_200");
    fallback.push("ott+10_50_bd=off:drc=off:fsr=off:nwc=1.1:sp=occurrence_300");
    fallback.push("ott+10_7_bs=off:drc=off:fsr=off:nwc=1.1:sp=occurrence_300");
    fallback.push("dis+10_128_bs=unit_only:drc=off:fsr=off:gsp=input_only:nwc=10_300");
    fallback.push("lrs+10_8:1_nwc=1:sfv=off:sp=reverse_arity_900");
    fallback.push("ott+10_8_bd=off:bs=off:drc=off:fsr=off:fde=none:nwc=2:sp=occurrence_300");
    fallback.push("ott+10_8:1_bs=off:bsr=on:nwc=1.3_300");
    fallback.push("lrs+10_2:1_bd=off:bs=off:drc=off:fsr=off:nwc=2.5_300");
    fallback.push("dis+10_5_bs=off:drc=off:fsr=off:nwc=1.5:sp=occurrence_600");
    fallback.push("ott+10_1_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.3_600");
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
    quick.push("dis+1_24_bs=off:cond=on:fde=none:nwc=1.5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_31");
    quick.push("dis+11_64_bs=off:bfnt=on:cond=fast:gs=on:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_1");
    quick.push("dis+1_128_bs=off:bfnt=on:cond=fast:lcm=predicate:nwc=4:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_3");
    quick.push("dis-11_1024_bs=off:bfnt=on:gs=on:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:sp=occurrence_12");
    quick.push("dis+1_5:4_cond=fast:ep=RSTC:fsr=off:gs=on:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:spl=sat:sp=occurrence:urr=on_43");
    quick.push("dis+1_24_bs=off:bfnt=on:cond=fast:lcm=predicate:nwc=10:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_164");
    quick.push("ott+10_3_bs=off:bfnt=on:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_88");
    break;

  case Property::HEQ:
    quick.push("dis+1_14_bs=off:cond=fast:ecs=on:fde=none:gs=on:lcm=predicate:nwc=2:ssec=off:sac=on:sio=off:spo=on:sp=occurrence_1");
    quick.push("dis+2_5:1_bs=off:bfnt=on:lcm=predicate:nwc=2:ptb=off:ssec=off:sio=off:spl=sat:sp=reverse_arity_2");
    quick.push("ott+3_1024_bs=off:bfnt=on:nwc=10:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat_12");
    quick.push("ins+4_12_bs=off:bfnt=on:cond=fast:igbrr=0.8:igrr=128/1:igrp=4000:igrpq=1.5:lcm=predicate:nwc=2:ptb=off:ssec=off:spl=off:sp=occurrence_67");
    quick.push("dis+2_1024_bd=off:bs=off:cond=fast:fsr=off:nwc=4:ptb=off:ssec=off:spl=backtracking_844");
    break;
    
  case Property::PEQ:
    quick.push("dis+10_40_bs=off:cond=fast:fde=none:gsp=input_only:nwc=1.5:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat:sp=reverse_arity_3");
    quick.push("ott+11_8_bs=off:bfnt=on:fde=none:gs=on:nwc=4:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat:sp=occurrence_4");
    quick.push("ins+1011_4:1_bs=off:bfnt=on:igbrr=0.8:igrr=2/1:igrp=100:igrpq=2.0:igwr=on:nwc=2.5:ptb=off:ssec=off:sos=all:spl=off_3");
    quick.push("dis+2_3_bs=unit_only:ep=on:fsr=off:gs=on:nwc=3:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:urr=on:updr=off_357");
    quick.push("ins+1_6_bs=off:bfnt=on:br=off:cond=fast:igbrr=0.0:igrr=1/2:igrp=400:igrpq=2.0:igwr=on:nwc=1.1:ptb=off:ssec=off:spl=off:urr=on_61");
    break;

  case Property::HNE:
    quick.push("dis+3_6_bs=off:cond=fast:gs=on:nwc=1.2:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sp=occurrence_1");
    quick.push("dis+10_64_bs=off:bfnt=on:cond=fast:ecs=on:gs=on:lcm=predicate:nwc=1:ssec=off:sp=occurrence_2");
    quick.push("dis+10_10_bs=off:bms=on:cond=fast:gsp=input_only:nwc=5:ssec=off:sac=on:sio=off:spo=on_1");
    quick.push("dis+11_20_bs=off:cond=fast:nwc=1.3:nicw=on:sac=on:sio=off_4");
    quick.push("dis-11_32_bs=off:nwc=2.5:ptb=off:ssec=off:sio=off:spl=off_24");
    break;

  case Property::NNE:
    quick.push("dis+11_4_bs=off:cond=fast:gs=on:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=all_dependent:sp=occurrence_2");
    quick.push("dis+11_16_bs=off:bfnt=on:cond=on:gsp=input_only:gs=on:lcm=predicate:nwc=1.2:ptb=off:ssec=off:sac=on:sio=off:spl=sat_13");
    quick.push("ins+11_12_bs=off:bfnt=on:gsp=input_only:igbrr=0.9:igrr=4/1:igrp=400:igrpq=1.5:nwc=5:ptb=off:ssec=off:sos=on:spl=off_188");
    quick.push("dis+4_14_bs=off:cond=on:gs=on:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat_96");
    break;

  case Property::FEQ:
    quick.push("dis+3_2:3_bs=off:cond=fast:gs=on:nwc=2:ptb=off:ssec=off:sio=off_1");
    quick.push("dis+1_1024_bs=off:bfnt=on:fde=none:gs=on:lcm=predicate:nwc=1.2:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat_47");
    quick.push("ott+11_1024_bs=off:bms=on:lcm=predicate:nwc=5:sio=off_44");
    quick.push("ins-2_3:1_bs=off:bsr=unit_only:ep=RSTC:gs=on:igbrr=0.5:igrr=1/64:igrpq=1.2:igwr=on:lcm=predicate:nwc=5:ptb=off:ssec=off:sos=on:sio=off:spl=off:urr=on_1");
    quick.push("ins-3_4:1_bs=off:bsr=unit_only:bfnt=on:cond=on:fsr=off:gs=on:igbrr=0.2:igrp=2000:igrpq=2.0:nwc=2.5:ptb=off:ssec=off:sio=off:spl=off_48");
    quick.push("dis+3_1024_bs=off:bfnt=on:gs=on:nwc=4:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_541");
    quick.push("dis+4_40_bs=off:bfnt=on:cond=on:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:urr=on_285");
    quick.push("dis+11_1024_bs=off:bfnt=on:cond=on:gsp=input_only:gs=on:nwc=1.7:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:urr=on_132");
    quick.push("dis+1_7_bfnt=on:cond=on:fde=none:lcm=predicate:nwc=2:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:sp=occurrence:urr=on:updr=off_272");
    quick.push("ins+1_40_bs=off:bsr=unit_only:bfnt=on:cond=on:ep=RSTC:igbrr=0.5:igrr=128/1:igrp=100:igrpq=1.5:igwr=on:nwc=1.7:ptb=off:ssec=off:sos=on:sio=off:spl=off_27");
    break;

  case Property::FNE:
    quick.push("dis+1_32_bs=off:bfnt=on:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sgo=on:sio=off:spo=on:spl=sat:sp=occurrence_51");
    quick.push("ins+3_28_bs=off:bfnt=on:br=off:igbrr=0.6:igrr=1/128:igrp=200:igrpq=2.0:igwr=on:nwc=4:ptb=off:ssec=off:sos=all:spl=off:urr=on_31");
    quick.push("dis+11_12_bs=off:cond=fast:gs=on:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sp=reverse_arity_41");
    quick.push("dis-11_12_bs=off:bms=on:bfnt=on:cond=fast:ecs=on:lcm=predicate:nwc=4:nicw=on:ssec=off:sio=off:spl=off:sp=occurrence_199");
    quick.push("dis+3_2:3_bs=off:bfnt=on:fsr=off:gs=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:urr=on_30");
    quick.push("dis+2_1024_bs=off:ecs=on:fsr=off:gsp=input_only:nwc=5:ssec=off:sio=off:spl=off_431");
    quick.push("ott+1_1024_bs=off:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sac=on:spl=sat:updr=off_241");
    quick.push("ins+3_40_bs=off:bfnt=on:igbrr=0.4:igrr=128/1:igrp=200:igrpq=1.5:igwr=on:nwc=4:ptb=off:ssec=off:sos=on:spl=off_123");
    break;

  case Property::EPR:
    quick.push("ott+11_12_bs=off:gs=on:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.1:ssnc=none:updr=off_33");
    quick.push("ins+1003_4:1_bs=off:bsr=on:flr=on:fsr=off:igbrr=0.0:igrp=2000:igrpq=1.3:nwc=5:ptb=off:ssec=off:sio=off:spl=off_1");
    quick.push("ott+2_40_bs=off:gs=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sio=off:spl=sat_37");
    quick.push("ott+1_24_bs=off:cond=fast:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:spo=on:spl=sat:urr=on_268");
    break;
 
  case Property::UEQ:
    quick.push("dis+10_2:1_bs=off:bsr=unit_only:fsr=off:nwc=3:sp=occurrence_1");
    quick.push("dis+10_20_bs=off:bfnt=on:cond=on:fsr=off:fde=none:gs=on:lcm=predicate:nwc=4:ptb=off:ssec=off:sio=off:spo=on:spl=sat:sp=reverse_arity_67");
    quick.push("ins+3_6_bs=off:bfnt=on:br=off:fsr=off:igbrr=0.9:igrp=100:igrpq=1.5:igwr=on:nwc=4:ptb=off:ssec=off:spl=off:urr=on_41");
    quick.push("ott+1_128_bfnt=on:cond=fast:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat:sp=occurrence:urr=on_124");
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
    break;

  case Property::FEQ: 
    fallback.push("ott+11_12_bs=off:gs=on:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.1:ssnc=none:updr=off_300");
    fallback.push("ins+11_12_bs=off:bfnt=on:gsp=input_only:igbrr=0.9:igrr=4/1:igrp=400:igrpq=1.5:nwc=5:ptb=off:ssec=off:sos=on:spl=off_300");
    fallback.push("dis+1_1024_bs=off:bfnt=on:lcm=predicate:nwc=1.2:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sp=reverse_arity_300");
    fallback.push("dis+2_3_bs=unit_only:ep=on:fsr=off:gs=on:nwc=3:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:urr=on:updr=off_600");
    fallback.push("ins+4_12_bs=off:bfnt=on:cond=fast:igbrr=0.8:igrr=128/1:igrp=4000:igrpq=1.5:lcm=predicate:nwc=2:ptb=off:ssec=off:spl=off:sp=occurrence_300");
    fallback.push("ott+1_128_bfnt=on:cond=fast:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat:sp=occurrence:urr=on_300");
    fallback.push("dis-11_32_bs=off:nwc=2.5:ptb=off:ssec=off:sio=off:spl=off_300");
    fallback.push("dis+11_16_bs=off:bfnt=on:cond=on:gsp=input_only:gs=on:lcm=predicate:nwc=1.2:ptb=off:ssec=off:sac=on:sio=off:spl=sat_300");
    fallback.push("dis+1_14_bs=off:cond=fast:ecs=on:fde=none:gs=on:lcm=predicate:nwc=2:ssec=off:sac=on:sio=off:spo=on:sp=occurrence_300");
    fallback.push("dis+1_24_bs=off:bfnt=on:cond=fast:lcm=predicate:nwc=10:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_300");
    fallback.push("dis+2_5:1_bs=off:bfnt=on:lcm=predicate:nwc=2:ptb=off:ssec=off:sio=off:spl=sat:sp=reverse_arity_300");
    fallback.push("ins+1_6_bs=off:bfnt=on:br=off:cond=fast:igbrr=0.0:igrr=1/2:igrp=400:igrpq=2.0:igwr=on:nwc=1.1:ptb=off:ssec=off:spl=off:urr=on_300");
    fallback.push("dis+3_6_bs=off:cond=fast:gs=on:nwc=1.2:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sp=occurrence_300");
    fallback.push("dis+1_24_bs=off:cond=on:fde=none:nwc=1.5:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_300");
    fallback.push("dis-11_1024_bs=off:bfnt=on:gs=on:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:sp=occurrence_300");
    fallback.push("dis+1_5:4_cond=fast:ep=RSTC:fsr=off:gs=on:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:spl=sat:sp=occurrence:urr=on_300");
    fallback.push("dis+10_2:1_bs=off:bsr=unit_only:fsr=off:nwc=3:sp=occurrence_300");
    fallback.push("dis+4_14_bs=off:cond=on:gs=on:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat_300");
    fallback.push("dis+11_64_bs=off:bfnt=on:cond=fast:gs=on:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_300");
    fallback.push("ott+3_1024_bs=off:bfnt=on:nwc=10:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat_300");
    fallback.push("ott+1_24_bs=off:cond=fast:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:spo=on:spl=sat:urr=on_300");
    fallback.push("ins+1003_4:1_bs=off:bsr=on:flr=on:fsr=off:igbrr=0.0:igrp=2000:igrpq=1.3:nwc=5:ptb=off:ssec=off:sio=off:spl=off_300");
    fallback.push("dis+10_64_bs=off:bfnt=on:cond=fast:ecs=on:gs=on:lcm=predicate:nwc=1:ssec=off:sp=occurrence_300");
    fallback.push("ott+11_8_bs=off:bfnt=on:fde=none:gs=on:nwc=4:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat:sp=occurrence_300");
    fallback.push("ott+10_3_bs=off:bfnt=on:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_300");
    fallback.push("dis+11_4_bs=off:cond=fast:gs=on:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:sser=off:ssfq=2.0:ssnc=all_dependent:sp=occurrence_100");
    fallback.push("ins+3_6_bs=off:bfnt=on:br=off:fsr=off:igbrr=0.9:igrp=100:igrpq=1.5:igwr=on:nwc=4:ptb=off:ssec=off:spl=off:urr=on_300");
    fallback.push("ott+2_40_bs=off:gs=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sio=off:spl=sat_300");
    fallback.push("dis+10_10_bs=off:bms=on:cond=fast:gsp=input_only:nwc=5:ssec=off:sac=on:sio=off:spo=on_200");
    fallback.push("dis+10_40_bs=off:cond=fast:fde=none:gsp=input_only:nwc=1.5:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=sat:sp=reverse_arity_300");
    fallback.push("dis+1_128_bs=off:bfnt=on:cond=fast:lcm=predicate:nwc=4:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_300");
    fallback.push("dis+11_20_bs=off:cond=fast:nwc=1.3:nicw=on:sac=on:sio=off_300");
    fallback.push("ins+1011_4:1_bs=off:bfnt=on:igbrr=0.8:igrr=2/1:igrp=100:igrpq=2.0:igwr=on:nwc=2.5:ptb=off:ssec=off:sos=all:spl=off_300");
    fallback.push("dis+10_20_bs=off:bfnt=on:cond=on:fsr=off:fde=none:gs=on:lcm=predicate:nwc=4:ptb=off:ssec=off:sio=off:spo=on:spl=sat:sp=reverse_arity_300");
    fallback.push("dis+2_1024_bd=off:bs=off:cond=fast:fsr=off:nwc=4:ptb=off:ssec=off:spl=backtracking_900");
    break;

  case Property::FNE:
    fallback.push("dis+1_32_bs=off:bfnt=on:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sgo=on:sio=off:spo=on:spl=sat:sp=occurrence_300");
    fallback.push("dis+1_1024_bs=off:bfnt=on:fde=none:gs=on:lcm=predicate:nwc=1.2:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat_300");
    fallback.push("dis+11_12_bs=off:cond=fast:gs=on:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sp=reverse_arity_300");
    fallback.push("ins+3_40_bs=off:bfnt=on:igbrr=0.4:igrr=128/1:igrp=200:igrpq=1.5:igwr=on:nwc=4:ptb=off:ssec=off:sos=on:spl=off_300");
    fallback.push("dis+3_1024_bs=off:bfnt=on:gs=on:nwc=4:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_600");
    fallback.push("ott+11_1024_bs=off:bms=on:lcm=predicate:nwc=5:sio=off_300");
    fallback.push("dis-11_12_bs=off:bms=on:bfnt=on:cond=fast:ecs=on:lcm=predicate:nwc=4:nicw=on:ssec=off:sio=off:spl=off:sp=occurrence_300");
    fallback.push("dis+2_1024_bs=off:ecs=on:fsr=off:gsp=input_only:nwc=5:ssec=off:sio=off:spl=off_600");
    fallback.push("dis+4_40_bs=off:bfnt=on:cond=on:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:urr=on_300");
    fallback.push("ins-3_4:1_bs=off:bsr=unit_only:bfnt=on:cond=on:fsr=off:gs=on:igbrr=0.2:igrp=2000:igrpq=2.0:nwc=2.5:ptb=off:ssec=off:sio=off:spl=off_300");
    fallback.push("ott+1_1024_bs=off:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sac=on:spl=sat:updr=off_300");
    fallback.push("dis+1_7_bfnt=on:cond=on:fde=none:lcm=predicate:nwc=2:nicw=on:ptb=off:ssec=off:sio=off:spl=sat:sp=occurrence:urr=on:updr=off_300");
    fallback.push("ins-2_3:1_bs=off:bsr=unit_only:ep=RSTC:gs=on:igbrr=0.5:igrr=1/64:igrpq=1.2:igwr=on:lcm=predicate:nwc=5:ptb=off:ssec=off:sos=on:sio=off:spl=off:urr=on_300");
    fallback.push("dis+3_2:3_bs=off:bfnt=on:fsr=off:gs=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:urr=on_300");
    fallback.push("dis+3_2:3_bs=off:cond=fast:gs=on:nwc=2:ptb=off:ssec=off:sio=off_300");
    fallback.push("ins+3_28_bs=off:bfnt=on:br=off:igbrr=0.6:igrr=1/128:igrp=200:igrpq=2.0:igwr=on:nwc=4:ptb=off:ssec=off:sos=all:spl=off:urr=on_300");
    fallback.push("dis+11_1024_bs=off:bfnt=on:cond=on:gsp=input_only:gs=on:nwc=1.7:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:urr=on_300");
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
  Property::Category cat = property.category();
  unsigned prop = property.props();
  unsigned atoms = property.atoms();

  quick.push("ott+11_12_bs=off:gs=on:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sser=off:ssfp=10000:ssfq=1.1:ssnc=none:updr=off_3");
  quick.push("ott+10_8:1_bs=off:bsr=unit_only:cond=fast:drc=off:nwc=1.5:nicw=on:ptb=off:ssec=off:spo=on:spl=sat:sser=off:ssnc=none:urr=on_166");
  quick.push("ins+11_14_bs=off:flr=on:gsp=input_only:igbrr=0.7:igrr=1/8:igrp=4000:igrpq=1.5:igwr=on:lcm=predicate:nwc=3:ptb=off:ssec=off:spl=off:urr=on_55");
  quick.push("ins+1003_4:1_bs=off:bsr=on:flr=on:fsr=off:igbrr=0.0:igrp=2000:igrpq=1.3:nwc=5:ptb=off:ssec=off:sio=off:spl=off_1");
  quick.push("ins+4_14_bs=off:cond=on:flr=on:igbrr=0.2:igrr=1/128:igrp=700:igrpq=1.2:igwr=on:nwc=1:ptb=off:ssec=off:spl=off:urr=on_41");
  quick.push("dis+1_8:1_bs=off:drc=off:flr=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=sat:sser=off:ssfp=40000:ssfq=1.2_164");
  quick.push("ott+2_40_bs=off:gs=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sio=off:spl=sat_26");
  quick.push("dis+1_20_bs=off:nwc=4:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=sat:ssfp=4000:ssfq=1.1:sp=occurrence:updr=off_285");
  quick.push("ott+1_24_bs=off:cond=fast:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:spo=on:spl=sat:urr=on_268");
  quick.push("ins+1_5_bs=off:bsr=on:drc=off:gs=on:igbrr=0.0:igrr=1/32:igrp=400:igrpq=2.0:igwr=on:lcm=predicate:nwc=2:ptb=off:ssec=off:sio=off:spl=off:sp=reverse_arity:urr=on:updr=off_264");
  quick.push("dis+3_10_bs=off:drc=off:ecs=on:fsr=off:nwc=1.2:nicw=on:ssec=off:sio=off:spl=off_477");
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
    int remainingTime = env.remainingTime()/100;
    if(remainingTime<=0) {
      return false;
    }
    // cast to unsigned is OK since realTimeRemaining is positive
    if(sliceTime > (unsigned)remainingTime) {
      sliceTime = remainingTime;
    }
    env.beginOutput();
    env.out()<<"% remaining time: "<<remainingTime<<" next slice time: "<<sliceTime<<endl;
    env.endOutput();
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
  int stl = opt.simulatedTimeLimit();
  if (stl) {
    opt.setSimulatedTimeLimit(int(stl * SLOWNESS));
  }
  return runSlice(opt);
}

}
}
