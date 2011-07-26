/**
 * @file CASCMode.cpp
 * Implements class CASCMode.
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Stack.hpp"
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
  exit(3);
}

bool CASCMode::perform()
{
  CALL("CASCMode::perform/0");

  Property::Category cat = _property->category();
  unsigned prop = _property->props();
  unsigned atoms = _property->atoms();

  cout << "Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!\n";

  const char** quickSlices;
  const char** fallbackSlices;

  switch (cat) {
  case Property::NEQ:
    {
      if (prop == 131079) {
	const char* quick[] = {
	  "ott+1011_2:3_bs=off:bsr=unit_only:ep=on:gsp=input_only:nwc=3:sac=on:sgo=on:spo=on:sfv=off_35",
	  "ott+11_2_bd=off:bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:spo=on:spl=backtracking:sp=reverse_arity_53",
	  "dis+11_40_bsr=unit_only:cond=fast:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:spl=backtracking:sfv=off_243",
	  "dis+1011_14_bd=off:bs=off:bsr=on:cond=fast:ep=on:gsp=input_only:lcm=reverse:nwc=2:sswn=on:sswsr=on:sac=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_111",
	  "ott+11_28_bs=off:cond=on:drc=off:ecs=on:fde=none:gs=on:nwc=1.7:ssec=off:sgo=on:sio=off:sp=reverse_arity_1",
	  "dis+11_1_bsr=unit_only:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sswsr=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence:updr=off_24",
	  "dis+11_12_bs=unit_only:cond=on:flr=on:fde=none:lcm=reverse:nwc=1.5:sswn=on:sswsr=on:sgo=on:sfv=off:sp=reverse_arity_115",
	  "lrs+1002_2:1_bd=off:bs=unit_only:bsr=on:cond=on:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=4:ptb=off:ssec=off:stl=60:sac=on:sio=off:sp=occurrence_8",
	  "ott+11_3_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:fde=none:nwc=10:ptb=off:ssec=off:sac=on:spo=on:spl=backtracking:sfv=off:updr=off_105",
	  "dis+1011_10_bd=off:bs=unit_only:bsr=on:bms=on:cond=fast:ep=on:lcm=predicate:nwc=1:nicw=on:ssec=off:sac=on:sgo=on:sio=off:spo=on:sfv=off:sp=occurrence:updr=off_82",
	  "ott+11_3_bs=unit_only:bsr=unit_only:cond=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.1:ptb=off:ssec=off:sac=on:sgo=on:spo=on:spl=backtracking:sfv=off:sp=occurrence:updr=off_57",
	  "dis+1_50_cond=fast:lcm=predicate:nwc=3.0_177",
	  "ott+11_5:1_bs=off:cond=fast:drc=off:ep=on:fsr=off:gsp=input_only:nwc=4:nicw=on:sswn=on:sac=on:sgo=on:sp=occurrence_860",
	  "dis+11_6_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sgo=on:sio=off:swb=on:sp=occurrence:updr=off_60",
	  "lrs+4_4_bd=off:cond=on:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=30:sos=on:spl=backtracking:sp=reverse_arity_144",
	  "dis+3_8_bd=off:bs=off:flr=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_144",
	  0
	};
	quickSlices = quick;
      }
      else if (prop == 3) {
	const char* quick[] = {
	  "dis+11_6_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sgo=on:sio=off:swb=on:sp=occurrence:updr=off_10",
	  "dis+1010_4:1_bs=off:bsr=unit_only:cond=on:ep=RS:gs=on:lcm=reverse:nwc=4:sswn=on:sos=on:spo=on:sp=occurrence_1",
	  "dis-1002_3:2_bs=off:cond=on:drc=off:ep=RS:flr=on:lcm=predicate:nwc=10:ssec=off:sgo=on:sio=off:spo=on:sp=reverse_arity_4",
	  "ott+1011_3_bs=off:drc=off:ep=on:fde=none:gsp=input_only:nwc=1:sgo=on:sio=off:spo=on:updr=off_84",
	  "ott-1010_5:4_bd=off:bs=off:bms=on:cond=on:drc=off:ep=on:lcm=predicate:nwc=1:nicw=on:ssec=off:sd=3:ss=axioms:sos=on:sio=off:sp=reverse_arity:urr=on_6",
	  "lrs-4_1_bd=off:bs=off:bms=on:ecs=on:gsp=input_only:nicw=on:ssec=off:stl=60:sos=on:sio=off:spl=off_47",
	  "dis+2_28_bs=off:br=off:cond=fast:drc=off:ecs=on:ep=on:gsp=input_only:lcm=reverse:nwc=2.5:nicw=on:ssec=off:sd=1:ss=axioms:st=3.0:sos=on:sac=on:spo=on:sp=reverse_arity:urr=on_3",
	  "dis+11_5:1_cond=fast:ep=on:gsp=input_only:nwc=10:sswn=on:sswsr=on_8",
	  "lrs+4_4_bd=off:cond=on:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=30:sos=on:spl=backtracking:sp=reverse_arity_43",
	  "lrs-1010_64_bd=off:bs=off:drc=off:nwc=2:ssec=off:stl=30:sac=on:sgo=on:spo=on_18",
	  "dis-1_64_bsr=on:cond=fast:ecs=on:flr=on:fsr=off:lcm=reverse:nwc=1.7:ssec=off:sos=on:sagn=off:sac=on:sgo=on:sio=off:spo=on:sfv=off:sp=reverse_arity_1",
	  "dis+1_5:1_bd=off:bs=unit_only:cond=fast:drc=off:flr=on:fde=none:lcm=reverse:nwc=10:ptb=off:ssec=off:sio=off:spo=on:swb=on_4",
	  "ott+1_2:1_bd=off:bs=off:bms=on:cond=fast:ep=on:flr=on:fsr=off:nwc=5:spo=on:sfv=off:sp=reverse_arity:updr=off_1",
	  "dis-1010_5:1_bs=off:cond=fast:ep=R:lcm=reverse:nwc=1.2:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:sfv=off:sp=occurrence_29",
	  "dis-1002_8:1_bs=off:br=off:drc=off:ecs=on:ep=on:fde=none:gs=on:nwc=1.2:nicw=on:ssec=off:sd=5:ss=axioms:st=1.2:sos=on:sac=on:sio=off:sp=reverse_arity:urr=on_2",
	  "dis+10_5_bs=off:cond=on:flr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sp=occurrence_138",
	  "dis+1010_6_bd=off:nwc=10.0:ssec=off:sac=on:sp=occurrence_21",
	  "dis+1011_10_bd=off:bs=unit_only:bsr=on:bms=on:cond=fast:ep=on:lcm=predicate:nwc=1:nicw=on:ssec=off:sac=on:sgo=on:sio=off:spo=on:sfv=off:sp=occurrence:updr=off_232",
	  "ott+11_2_bd=off:bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:spo=on:spl=backtracking:sp=reverse_arity_247",
	  "ott+11_5:1_bs=off:cond=fast:drc=off:ep=on:fsr=off:gsp=input_only:nwc=4:nicw=on:sswn=on:sac=on:sgo=on:sp=occurrence_107",
	  "dis-1004_8:1_bs=off:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=10:nicw=on:ssec=off:sp=reverse_arity_222",
	  "dis+11_40_bd=off:bs=off:cond=fast:ep=on:flr=on:gsp=input_only:gs=on:lcm=reverse:nwc=5:ptb=off:ssec=off:sac=on:sio=off:swb=on:sfv=off_147",
	  "lrs+1_4:1_bd=off:bs=off:cond=on:fde=none:lcm=predicate:stl=60:sos=on_580",
	  "lrs+2_2_bd=off:bs=unit_only:bsr=unit_only:cond=fast:drc=off:flr=on:lcm=predicate:nwc=1.5:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:swb=on_153",
	  "dis+2_8:1_bs=off:br=off:cond=fast:drc=off:ep=RST:flr=on:fsr=off:fde=none:gsp=input_only:nwc=1.1:ssec=off:sac=on:spo=on:sp=reverse_arity:urr=on_167",
	  "dis+10_8_bs=off:cond=on:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_379",
	  "dis+1010_8:1_bs=off:cond=fast:drc=off:ep=on:fde=none:lcm=reverse:nwc=2:sos=on:sac=on:sp=reverse_arity_1",
	  "dis+3_14_bs=off:drc=off:ecs=on:fde=none:gsp=input_only:nwc=1.2:nicw=on:ssec=off:sac=on:sio=off:sp=occurrence:urr=on_17",
	  "lrs+1002_2:1_bd=off:bs=unit_only:bsr=on:cond=on:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=4:ptb=off:ssec=off:stl=60:sac=on:sio=off:sp=occurrence_21",
	  0
	};
	quickSlices = quick;
      }
      else if (prop == 1) {
	const char* quick[] = {
	  "dis+11_40_bd=off:bs=off:cond=fast:ep=on:flr=on:gsp=input_only:gs=on:lcm=reverse:nwc=5:ptb=off:ssec=off:sac=on:sio=off:swb=on:sfv=off_2",
	  "ott+1011_2:3_bs=off:bsr=unit_only:ep=on:gsp=input_only:nwc=3:sac=on:sgo=on:spo=on:sfv=off_1",
	  "dis-1002_8:1_bs=off:br=off:drc=off:ecs=on:ep=on:fde=none:gs=on:nwc=1.2:nicw=on:ssec=off:sd=5:ss=axioms:st=1.2:sos=on:sac=on:sio=off:sp=reverse_arity:urr=on_13",
	  "ott+11_28_bs=off:cond=on:drc=off:ecs=on:fde=none:gs=on:nwc=1.7:ssec=off:sgo=on:sio=off:sp=reverse_arity_27",
	  "lrs+1011_20_bd=off:bs=off:bsr=on:cond=on:drc=off:fsr=off:gs=on:lcm=reverse:nwc=3:ssec=off:stl=30:sos=on:sagn=off:sio=off:spl=off_2",
	  "lrs+1002_2:3_bs=off:cond=on:drc=off:ep=on:nwc=1.7:nicw=on:ptb=off:ssec=off:stl=30:sagn=off:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_20",
	  "ott+1011_3_bs=off:drc=off:ep=on:fde=none:gsp=input_only:nwc=1:sgo=on:sio=off:spo=on:updr=off_21",
	  "dis+11_6_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sgo=on:sio=off:swb=on:sp=occurrence:updr=off_4",
	  "dis-1002_3:2_bs=off:cond=on:drc=off:ep=RS:flr=on:lcm=predicate:nwc=10:ssec=off:sgo=on:sio=off:spo=on:sp=reverse_arity_4",
	  "dis+10_128_bs=off:cond=on:drc=off:flr=on:fsr=off:fde=none:lcm=predicate:nwc=2:ptb=off:ssec=off:sac=on:swb=on_112",
	  "ott+11_2_bd=off:bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:spo=on:spl=backtracking:sp=reverse_arity_140",
	  "dis+2_4_bs=off:cond=fast:drc=off:ep=RST:fsr=off:fde=none:lcm=reverse:nwc=2:ssec=off:sac=on:sio=off:spo=on:sp=reverse_arity:urr=on_81",
	  "lrs+1003_8:1_bd=off:drc=off:fde=none:gsp=input_only:nwc=5:ptb=off:ssec=off:stl=180:swb=on:sfv=off:sp=reverse_arity_2",
	  "dis+1011_10_bd=off:bs=unit_only:bsr=on:bms=on:cond=fast:ep=on:lcm=predicate:nwc=1:nicw=on:ssec=off:sac=on:sgo=on:sio=off:spo=on:sfv=off:sp=occurrence:updr=off_48",
	  "ott+10_64_bd=off:bsr=unit_only:bms=on:fde=none:nwc=1.5:sswn=on:sswsr=on:sac=on:sgo=on:sio=off:spo=on:sfv=off:updr=off_121",
	  "lrs-1010_64_bd=off:bs=off:drc=off:nwc=2:ssec=off:stl=30:sac=on:sgo=on:spo=on_162",
	  "lrs+11_20_bs=off:cond=on:drc=off:flr=on:fsr=off:gs=on:nwc=2.5:ssec=off:stl=60:sgo=on:spo=on:sp=reverse_arity:urr=on:updr=off_267",
	  "dis+11_40_bsr=unit_only:cond=fast:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:spl=backtracking:sfv=off_590",
	  "dis+1_2:1_drc=off:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sio=off:spl=backtracking:sp=reverse_arity:updr=off_575",
	  "dis-1010_3:1_bd=off:ep=R:flr=on:gsp=input_only:lcm=predicate:nwc=4.0:sswn=on:sswsr=on:sio=off_3",
	  "dis+3_14_bs=off:drc=off:ecs=on:fde=none:gsp=input_only:nwc=1.2:nicw=on:ssec=off:sac=on:sio=off:sp=occurrence:urr=on_93",
	  0
	};
	quickSlices = quick;
      }
      else {
	const char* quick[] = {
	  "dis+1010_6_bd=off:nwc=10.0:ssec=off:sac=on:sp=occurrence_1",
	  "ott+1011_2:3_bs=off:bsr=unit_only:ep=on:gsp=input_only:nwc=3:sac=on:sgo=on:spo=on:sfv=off_2",
	  "dis-1010_5:1_bs=off:cond=fast:ep=R:lcm=reverse:nwc=1.2:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:sfv=off:sp=occurrence_8",
	  "ott-1010_128_bd=off:bs=off:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=1:nicw=on:sswn=on:sswsr=on:sos=on:sac=on:sfv=off:sp=reverse_arity:updr=off_4",
	  "lrs+1011_20_bd=off:bs=off:bsr=on:cond=on:drc=off:fsr=off:gs=on:lcm=reverse:nwc=3:ssec=off:stl=30:sos=on:sagn=off:sio=off:spl=off_14",
	  "ott+1_2:1_bd=off:bs=off:bms=on:cond=fast:ep=on:flr=on:fsr=off:nwc=5:spo=on:sfv=off:sp=reverse_arity:updr=off_1",
	  "ott+10_50_bd=off:bms=on:cond=on:drc=off:flr=on:fde=none:gs=on:lcm=predicate:nwc=2.5:nicw=on:sswn=on:sos=on:sac=on:sio=off:spo=on:sp=occurrence:updr=off_1",
	  "dis+3_14_bs=off:drc=off:ecs=on:fde=none:gsp=input_only:nwc=1.2:nicw=on:ssec=off:sac=on:sio=off:sp=occurrence:urr=on_5",
	  "dis+1010_2:3_bs=off:drc=off:ep=on:nwc=10:ssec=off:sos=on:sgo=on:sio=off:sp=occurrence_50",
	  "dis+11_12_bs=unit_only:cond=on:flr=on:fde=none:lcm=reverse:nwc=1.5:sswn=on:sswsr=on:sgo=on:sfv=off:sp=reverse_arity_16",
	  "ott+1011_3_bs=off:drc=off:ep=on:fde=none:gsp=input_only:nwc=1:sgo=on:sio=off:spo=on:updr=off_12",
	  "dis+1011_7_cond=on:drc=off:ecs=on:ep=on:gs=on:lcm=predicate:nwc=1.7:ssec=off:sos=on:sac=on:sgo=on:sp=reverse_arity_198",
	  "lrs-1010_12_bd=off:gsp=input_only:nwc=3.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:sp=reverse_arity:updr=off_91",
	  "dis+1010_2:1_bs=off:drc=off:ep=RS:fsr=off:fde=none:gsp=input_only:nwc=10:ssec=off:sio=off:sp=reverse_arity_33",
	  "dis-1_64_bsr=on:cond=fast:ecs=on:flr=on:fsr=off:lcm=reverse:nwc=1.7:ssec=off:sos=on:sagn=off:sac=on:sgo=on:sio=off:spo=on:sfv=off:sp=reverse_arity_4",
	  "lrs+4_4_bd=off:cond=on:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=30:sos=on:spl=backtracking:sp=reverse_arity_28",
	  "dis+1002_10_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_35",
	  "dis-1002_3:2_bs=off:cond=on:drc=off:ep=RS:flr=on:lcm=predicate:nwc=10:ssec=off:sgo=on:sio=off:spo=on:sp=reverse_arity_18",
	  "dis+4_10_bd=off:bs=off:cond=fast:fde=none:nwc=10.0:ptb=off:ssec=off:sgo=on:spl=backtracking:sp=reverse_arity_146",
	  "dis+11_6_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sgo=on:sio=off:swb=on:sp=occurrence:updr=off_507",
	  "lrs+1004_14_bd=off:cond=on:drc=off:ep=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=3:sswsr=on:stl=30:sio=off:spl=off:updr=off_230",
	  "dis+11_1_bsr=unit_only:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sswsr=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence:updr=off_4",
	  "dis+1011_50_bs=unit_only:gsp=input_only:lcm=reverse:nwc=1.7:ptb=off:ssec=off:sac=on:spo=on:spl=backtracking:updr=off_67",
	  0
	};
	quickSlices = quick;
      }
    }
    break;

  case Property::HEQ: {
    if (prop == 2) {
      const char* quick[] = {
	"lrs+2_1_bms=on:cond=on:ecs=on:flr=on:gsp=input_only:lcm=predicate:nicw=on:ssec=off:stl=60:sos=on:sac=on:sgo=on:spo=on:sp=reverse_arity_18",
	"ott+1011_128_bs=off:bsr=on:cond=on:drc=off:ep=on:flr=on:fsr=off:nwc=1:nicw=on:ssec=off:sagn=off:sac=on:sio=off:sfv=off:sp=occurrence:updr=off_680",
	"ott-1004_50_bs=off:bsr=unit_only:bms=on:drc=off:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:sswsr=on:sfv=off:updr=off_836",
	0
      };
      quickSlices = quick;
    }
    else {
      const char* quick[] = {
	"lrs+11_5:4_bs=off:bsr=unit_only:bms=on:cond=fast:flr=on:nwc=2.5:nicw=on:stl=60:sio=off_98",
	"lrs-1_32_bd=off:bs=off:bsr=on:cond=on:ecs=on:gsp=input_only:lcm=predicate:nwc=4:nicw=on:ssec=off:stl=60:sac=on:sio=off:spo=on:sp=occurrence_2",
	"lrs+1010_5_bd=off:bs=off:bms=on:fde=none:gsp=input_only:nwc=2.5:nicw=on:sswsr=on:stl=60:sgo=on:sio=off:sp=reverse_arity:updr=off_9",
	"dis+2_128_bs=off:drc=off:lcm=predicate:nwc=10:sac=on:sio=off:sp=occurrence_203",
	"dis+2_10_bd=off:bs=unit_only:bsr=unit_only:ep=RS:fsr=off:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_60",
	"ott+1011_128_bs=off:bsr=on:cond=on:drc=off:ep=on:flr=on:fsr=off:nwc=1:nicw=on:ssec=off:sagn=off:sac=on:sio=off:sfv=off:sp=occurrence:updr=off_698",
	"dis+2_40_bd=off:bs=off:cond=fast:fsr=off:gsp=input_only:nwc=4.0:ptb=off:ssec=off:sagn=off:sgo=on:sio=off:spl=backtracking:sp=reverse_arity_583",
	"lrs-11_1_bd=off:bs=off:cond=fast:drc=off:flr=on:lcm=predicate:nwc=2:nicw=on:stl=30:spo=on:sp=occurrence_284",
	"ott+1003_4_bd=off:bms=on:cond=fast:drc=off:ep=on:flr=on:fsr=off:nwc=1.3:sswn=on:sac=on:sgo=on:sio=off:spo=on:sfv=off:sp=reverse_arity:updr=off_821",
	0
      };
      quickSlices = quick;
    }
    break;
  }
    
  case Property::PEQ: {
    if (prop == 0) {
      const char* quick[] = {
	"lrs-4_2_bs=off:bms=on:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.2:nicw=on:stl=60:sac=on:sio=off:spo=on:sfv=off_162",
	"lrs-4_28_bd=off:flr=on:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_78",
	"lrs-11_7_bs=off:bms=on:drc=off:ep=on:nwc=1.5:sswn=on:sswsr=on:stl=60:sgo=on:sp=reverse_arity_114",
	"lrs+4_4_bd=off:bsr=unit_only:bms=on:cond=on:drc=off:ecs=on:flr=on:fsr=off:fde=none:gsp=input_only:nwc=5:nicw=on:ssec=off:stl=60:sac=on:sio=off:spo=on:sfv=off_218",
	"dis-4_40_bs=unit_only:bsr=on:drc=off:ep=on:nwc=10:nicw=on:ssec=off:sos=on:sio=off:spl=off:sp=reverse_arity_302",
	"dis-1_10_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:fsr=off:nwc=1.2:sswn=on:sagn=off:spo=on:sfv=off_563",
	"ott+1004_2_bd=off:bsr=on:drc=off:ep=on:fsr=off:gsp=input_only:nwc=1.5:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spl=backtracking:sfv=off_780",
	"dis-11_32_bd=off:bs=unit_only:cond=on:drc=off:fsr=off:fde=none:nwc=1.5:ptb=off:ssec=off:sac=on:sgo=on:spo=on:swb=on:sfv=off:sp=occurrence_598",
	"ott+1011_7_bs=off:drc=off:fde=none:gsp=input_only:nwc=2.5:ptb=off:ssec=off:sio=off:swb=on:sp=occurrence_330",
	"ott+2_3:2_bd=off:bs=unit_only:bsr=unit_only:cond=on:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:nwc=5:sswn=on:sgo=on:sio=off:sp=reverse_arity_709",
	0
      };
      quickSlices = quick;
      break;
    }
    else if (prop == 1) {
      const char* quick[] = {
	"dis-4_40_bs=unit_only:bsr=on:drc=off:ep=on:nwc=10:nicw=on:ssec=off:sos=on:sio=off:spl=off:sp=reverse_arity_1",
	"lrs+4_4_bd=off:bsr=unit_only:bms=on:cond=on:drc=off:ecs=on:flr=on:fsr=off:fde=none:gsp=input_only:nwc=5:nicw=on:ssec=off:stl=60:sac=on:sio=off:spo=on:sfv=off_2",
	"dis+4_28_bd=off:bs=off:cond=on:drc=off:nwc=4:ptb=off:ssec=off:sos=on:sac=on:sio=off:swb=on_14",
	"dis+10_2_bd=off:cond=on:ecs=on:flr=on:gsp=input_only:nwc=5.0:nicw=on:ssec=off:sio=off:spl=off:sp=occurrence:updr=off_5",
	"lrs+1003_5_flr=on:fde=none:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:updr=off_45",
	"dis+1004_2_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:flr=on:fsr=off:gsp=input_only:nwc=1.5:sswsr=on:sac=on:sio=off:spo=on:sfv=off_252",
	"dis-11_32_bd=off:bs=unit_only:cond=on:drc=off:fsr=off:fde=none:nwc=1.5:ptb=off:ssec=off:sac=on:sgo=on:spo=on:swb=on:sfv=off:sp=occurrence_534",
	"lrs-10_12_bd=off:bs=off:bms=on:cond=on:drc=off:ep=on:gsp=input_only:nwc=1.5:nicw=on:sswn=on:sswsr=on:stl=60:sfv=off_590",
	"ott-11_5_bd=off:bs=unit_only:bsr=unit_only:cond=on:drc=off:flr=on:fsr=off:nwc=10:ptb=off:ssec=off:swb=on:sp=occurrence_222",
	0
      };
      quickSlices = quick;
    }
    else {
      const char* quick[] = {
	"ott+2_28_bs=off:bms=on:drc=off:ecs=on:fde=none:gsp=input_only:nwc=1.1:ssec=off:sio=off:spl=off_156",
	"ott+4_6_bs=off:bsr=on:cond=on:drc=off:flr=on:fsr=off:gsp=input_only:nwc=4:sswn=on:sac=on:sp=reverse_arity_121",
	"lrs-4_28_bd=off:flr=on:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_41",
	"ins+11_24_bd=off:bs=off:cond=fast:drc=off:fde=none:igbrr=0.0:igrr=1/32:igrp=100:igrpq=1.2:igwr=on:nwc=3:ptb=off:ssec=off:spl=off_99",
	"dis+1004_128_cond=on:ep=on:flr=on:gsp=input_only:nwc=3.0:updr=off_117",
	"lrs+10_5_bsr=on:drc=off:ep=on:gsp=input_only:nwc=1.2:stl=60:sos=on:updr=off_424",
	"ott+4_128_bs=off:bms=on:cond=on:drc=off:fsr=off:nwc=1.1:ssec=off:sagn=off:sac=on:sgo=on:sio=off:spo=on:sfv=off_363",
	0
      };
      quickSlices = quick;
    }
    break;
  }

  case Property::HNE: {
    const char* quick[] = {
      "ott+11_40_bsr=unit_only:cond=fast:flr=on:fsr=off:gsp=input_only:nwc=1.1:ptb=off:ssec=off:spl=backtracking:sp=occurrence_13",
      "dis+11_50_bs=unit_only:bms=on:gsp=input_only:lcm=reverse:nwc=1.5:nicw=on:sio=off:sp=reverse_arity_48",
      "lrs+11_12_fsr=off:nwc=3:stl=60:sgo=on:sio=off:sp=reverse_arity_232",
      "dis+1011_20_bs=off:fsr=off:nwc=2:ssec=off:sio=off:spl=off:sp=occurrence_117",
      "dis+2_2:3_flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=5.0:sio=off:spl=off:updr=off_685",
      "tab+10_1_gsp=input_only:spl=off:tbsr=off:tfsr=off:tgawr=1/8:tglr=1/7:tipr=off:tlawr=1/8_90",
      "lrs+2_14_bs=off:flr=on:gsp=input_only:nwc=3.0:nicw=on:stl=60:sgo=on:spo=on:sp=reverse_arity_533",
      "dis+1_40_bs=off:ecs=on:fsr=off:lcm=predicate:nwc=5:ssec=off:sac=on:sgo=on:spo=on:sp=reverse_arity:updr=off_575",
      "lrs+1011_24_bs=off:cond=on:flr=on:fsr=off:lcm=reverse:nwc=1.3:ssec=off:stl=30:sagn=off:sio=off:sp=reverse_arity_218",
      0
    };
    quickSlices = quick;
    break;
  }

  case Property::NNE: {
    const char* quick[] = {
      "dis+1002_40_bd=off:cond=on:lcm=predicate:nwc=1.7:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_34",
      "dis+10_6_ecs=on:lcm=reverse:nwc=5.0:ssec=off:sio=off:spl=off:sp=reverse_arity:updr=off_2",
      "ott-1_50_bs=off:bsr=on:cond=fast:fsr=off:nwc=1.3:ssec=off:sos=on:sio=off:sp=reverse_arity:updr=off_1",
      "lrs+1011_32_bs=off:bsr=unit_only:flr=on:lcm=reverse:nwc=1.3:ptb=off:ssec=off:stl=60:sac=on:sio=off:spl=backtracking:sp=occurrence:updr=off_1",
      "dis+11_16_bs=off:fsr=off:gsp=input_only:lcm=reverse:nwc=1.2:sac=on:sgo=on:spo=on:sp=occurrence_44",
      "dis+1011_128_bs=off:gsp=input_only:nwc=1.7:nicw=on:sswsr=on:sos=on:spo=on:sp=reverse_arity_250",
      "dis-2_14_bs=off:cond=fast:flr=on:lcm=predicate:nicw=on:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spl=backtracking:updr=off_85",
      "dis+1010_20_lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_34",
      "dis+11_128_bs=off:cond=fast:flr=on:lcm=reverse:nwc=2:ptb=off:ssec=off:sac=on:updr=off_217",
      "dis-1002_7_flr=on:gsp=input_only:nwc=1.2:nicw=on:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity:updr=off_81",
      "dis+4_12_bs=off:gsp=input_only:lcm=predicate:nwc=4:ssec=off:spo=on:sp=occurrence:updr=off_234",
      "dis+1011_128_bs=off:cond=fast:flr=on:gsp=input_only:nwc=2.5:sswsr=on:sgo=on:sp=reverse_arity_297",
      "dis+1011_128_bs=off:flr=on:gsp=input_only:lcm=reverse:nwc=1.2:sswsr=on:sgo=on:spo=on:sp=occurrence_610",
      0
    };
    quickSlices = quick;
    break;
  }

  case Property::FEQ: {
    if (prop == 1) {
      if (atoms > 2000000) {
	const char* quick[] = {	  "dis+1_14_bsr=unit_only:cond=on:drc=off:ep=on:flr=on:fsr=off:fde=none:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sd=10:ss=included:st=1.5:sagn=off:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_1200",
	  "dis+10_3:1_bs=off:br=off:drc=off:fde=none:gs=on:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:st=5.0:sac=on:spo=on:spl=backtracking:sp=reverse_arity:urr=on_1200",
	  0
	};
	quickSlices = quick;
      }
      else { // atoms < 2M
	const char* quick[] = {
	  "lrs+3_2:3_bs=off:bsr=unit_only:bms=on:br=off:drc=off:fsr=off:fde=none:nwc=5:stl=60:sgo=on:sio=off:spo=on:sp=occurrence:urr=on_13",
	  "dis-2_20_flr=on:fde=none:lcm=predicate:nwc=1.3:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_17",
	  "ott-1004_2:3_bd=off:bs=off:cond=fast:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=backtracking:sp=occurrence_6",
	  "dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_1",
	  "lrs+11_20_bd=off:bs=off:drc=off:flr=on:fsr=off:gsp=input_only:gs=on:nwc=1.1:ptb=off:ssec=off:stl=90:sd=2:ss=axioms:st=2.0:sgo=on:spo=on:swb=on_3",
	  "dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_13",
	  "dis-3_128_bs=off:cond=on:drc=off:ep=R:gs=on:nwc=5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_1",
	  "lrs+11_40_bs=off:cond=fast:drc=off:flr=on:fde=none:gsp=input_only:nwc=10:ptb=off:ssec=off:stl=60:spo=on:spl=backtracking:sp=reverse_arity:updr=off_3",
	  "ins+1010_2:3_bs=off:cond=fast:drc=off:gs=on:igbrr=0.8:igrr=1/4:igrp=200:igrpq=2.0:igwr=on:nwc=10:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_124",
	  "dis+1010_40_bd=off:bms=on:cond=fast:drc=off:ecs=on:ep=on:fde=none:gsp=input_only:nwc=2:ssec=off:sgo=on:urr=on_107",
	  "lrs-1010_10_bd=off:bs=unit_only:cond=on:flr=on:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_206",
	  "lrs+1011_50_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.5:ptb=off:ssec=off:stl=90:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_203",
	  "lrs+1_3:2_bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=60:sgo=on:spl=backtracking:updr=off_328",
	  "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_560",
	  "ott+11_7_bs=off:cond=on:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sio=off:spl=backtracking:sp=occurrence:updr=off_348",
	  "dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_448",
	  0
	};
	quickSlices = quick;
      }
    }
    else if (prop == 2) {
      const char* quick[] = {
	"dis-1_128_bs=off:bsr=on:bms=on:fde=none:lcm=predicate:nwc=1:ssec=off:sac=on:urr=on_28",
	"ins+3_5_bs=off:flr=on:gsp=input_only:igbrr=0.1:igrr=1/32:igrp=700:igrpq=2.0:igwr=on:lcm=predicate:nwc=1:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_37",
	"ins+3_5:4_bsr=unit_only:cond=on:flr=on:gsp=input_only:igbrr=0.3:igrpq=1.5:nwc=3:ptb=off:ssec=off:spl=off:sp=reverse_arity_2290",
	"ott+10_50_bd=off:bs=off:bsr=unit_only:fde=none:gs=on:lcm=predicate:nwc=1:nicw=on:sac=on:sio=off:urr=on_566",
	"ins+2_12_bs=off:flr=on:gs=on:igbrr=1.0:igrr=1/64:igrp=400:igrpq=1.0:igwr=on:nwc=2:ptb=off:ssec=off:spl=off:sp=reverse_arity_46",
	"ott+1_64_bs=off:cond=on:lcm=predicate:nwc=1.1:sgo=on:spo=on:sp=occurrence:urr=on_232",
	"ins+10_24_bd=off:bs=off:br=off:drc=off:flr=on:fde=none:gsp=input_only:gs=on:igbrr=0.7:igrr=1/4:igrp=700:igrpq=2.0:igwr=on:lcm=reverse:nwc=1.1:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_300",
	"ins+4_50_bd=off:bs=off:br=off:cond=fast:drc=off:fsr=off:fde=none:gsp=input_only:gs=on:igbrr=0.6:igrr=1/64:igrp=200:igrpq=1.5:igwr=on:nwc=4:ptb=off:ssec=off:spl=off:sp=occurrence:urr=on_661",
	"ins-1010_2:3_bs=unit_only:cond=on:flr=on:fsr=off:gsp=input_only:gs=on:igbrr=0.9:igrp=100:igrpq=1.3:lcm=reverse:nwc=1.1:ptb=off:ssec=off:spl=off:sp=reverse_arity:updr=off_2148",
	"ott+11_50_bd=off:bs=off:cond=on:ecs=on:fde=none:gsp=input_only:lcm=predicate:nwc=4:nicw=on:ssec=off_1847",
	0
      };
      quickSlices = quick;
    }
    else if (prop == 131087) {
      if (atoms > 230000) {
	const char* quick[] = {
	  "dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_46",
	  "dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_50",
	  "dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_161",
	  "ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_49",
	  "dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_20",
	  "lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_37",
	  "dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_19",
	  "ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_44",
	  "lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_23",
	  "dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_98",
	  "ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_31",
	  "dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_91",
	  "dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_46",
	  "ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_213",
	  "dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_82",
	  "dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_93",
	  "lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_119",
	  "ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_123",
	  "ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_155",
	  "lrs+11_20_bd=off:bs=off:drc=off:flr=on:fsr=off:gsp=input_only:gs=on:nwc=1.1:ptb=off:ssec=off:stl=90:sd=2:ss=axioms:st=2.0:sgo=on:spo=on:swb=on_544",
	  "ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_36",
	  "ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_181",
	  0
	};
	quickSlices = quick;
      }
      else if (atoms > 120000) {
	const char* quick[] = {
	  "dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_16",
	  "dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_21",
	  "ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_19",
	  "lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:stl=30:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_20",
	  "ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_14",
	  "lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_12",
	  "dis-3_128_bd=off:bsr=unit_only:bms=on:ecs=on:ep=R:fsr=off:fde=none:nwc=1.3:ssec=off:sd=1:ss=included:st=2.0:sos=on:spo=on:sp=reverse_arity_15",
	  "ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_115",
	  "lrs+10_2_bs=off:br=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=30:sd=1:ss=axioms:st=5.0:sio=off:swb=on:sp=occurrence:urr=on_10",
	  "dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_86",
	  "dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_18",
	  "dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_14",
	  "ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_169",
	  "ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_71",
	  "ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_290",
	  "ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_106",
	  "ott+11_8:1_bs=off:cond=fast:drc=off:fsr=off:fde=none:nwc=4:sd=3:sgt=7:ss=axioms:sos=on:spo=on:sp=reverse_arity:updr=off_150",
	  "dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_172",
	  "dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_194",
	  "lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_882",
	  0
	};
	quickSlices = quick;
      }
      else if (atoms > 60000) {
	const char* quick[] = {
	  "dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_43",
	  "lrs+2_4:1_bs=off:br=off:drc=off:ecs=on:gs=on:lcm=reverse:nwc=2.5:ssec=off:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sio=off:sp=reverse_arity:urr=on_10",
	  "dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_19",
	  "dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_7",
	  "lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_7",
	  "ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_26",
	  "dis+1010_64_bd=off:bsr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_27",
	  "ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_9",
	  "dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_7",
	  "dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_66",
	  "ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_77",
	  "dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_89",
	  "dis-3_128_bd=off:bsr=unit_only:bms=on:ecs=on:ep=R:fsr=off:fde=none:nwc=1.3:ssec=off:sd=1:ss=included:st=2.0:sos=on:spo=on:sp=reverse_arity_6",
	  "lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_8",
	  "lrs-1010_12_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:stl=30:sd=4:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_113",
	  "dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_144",
	  "ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_95",
	  "lrs+10_3:2_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sd=2:ss=included:sio=off:spl=backtracking_182",
	  "dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_344",
	  "lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_878",
	  0
	};
	quickSlices = quick;
      }
      else if (atoms > 10000) {
	const char* quick[] = {
	  "lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_8",
	  "dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_2",
	  "ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_48",
	  "dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_16",
	  "ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_61",
	  "dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_23",
	  "dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_4",
	  "dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_9",
	  "dis-2_5:4_bd=off:bsr=on:cond=fast:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=2:sswsr=on:sos=on:sagn=off:sac=on:spo=on:sp=reverse_arity_4",
	  "lrs+10_2_bs=off:br=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=30:sd=1:ss=axioms:st=5.0:sio=off:swb=on:sp=occurrence:urr=on_3",
	  "dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_9",
	  "dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_29",
	  "ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_86",
	  "dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_53",
	  "ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_91",
	  "dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_94",
	  "ott+11_8:1_bs=off:cond=fast:drc=off:fsr=off:fde=none:nwc=4:sd=3:sgt=7:ss=axioms:sos=on:spo=on:sp=reverse_arity:updr=off_76",
	  "ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_7",
	  "ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_7",
	  "dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_36",
	  "dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_70",
	  "lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:stl=30:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_134",
	  "ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_73",
	  "lrs-1010_12_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:stl=30:sd=4:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_277",
	  "lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_779",
	  "dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_3",
	  "lrs+2_4:1_bs=off:br=off:drc=off:ecs=on:gs=on:lcm=reverse:nwc=2.5:ssec=off:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sio=off:sp=reverse_arity:urr=on_17",
	  "dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_135",
	  0
	};
	quickSlices = quick;
      }
      else  {
	const char* quick[] = {
	  "ins+1010_2:3_bs=off:cond=fast:drc=off:gs=on:igbrr=0.8:igrr=1/4:igrp=200:igrpq=2.0:igwr=on:nwc=10:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_6",
	  "lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_39",
	  "ott+10_8:1_bs=off:bms=on:br=off:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.3:ssec=off:sos=on:sgo=on:sio=off:urr=on_51",
	  "dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_13",
	  "dis+11_3:2_bs=off:drc=off:ep=R:flr=on:fde=none:nwc=1.7:sos=on:sac=on:sio=off:sp=occurrence_54",
	  "ott+1_3_bs=off:bms=on:cond=on:drc=off:ecs=on:fde=none:gsp=input_only:nwc=1.1:ssec=off:sac=on:sgo=on:spo=on_68",
	  "dis+11_12_bs=unit_only:cond=on:drc=off:ep=RS:flr=on:fsr=off:gsp=input_only:gs=on:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sos=on:sac=on:spo=on:swb=on:sp=reverse_arity:updr=off_22",
	  "dis+1011_1_bd=off:cond=fast:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=2:nicw=on:ptb=off:ssec=off:sgt=7:ss=axioms:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_39",
	  "ott-1004_2:3_bd=off:bs=off:cond=fast:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=backtracking:sp=occurrence_30",
	  "dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_43",
	  "dis+1_4_bs=off:bms=on:drc=off:ep=on:fde=none:lcm=reverse:nwc=4:ssec=off:sos=on:sac=on:sp=reverse_arity_69",
	  "lrs+2_5:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ecs=on:ep=RST:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=5:ssec=off:stl=60:sac=on:sio=off:urr=on_112",
	  "dis-1004_50_bs=off:drc=off:ep=R:flr=on:fsr=off:nwc=1.3:ssec=off:sos=on:spo=on:updr=off_44",
	  "dis-1002_3_bd=off:bs=off:cond=fast:drc=off:ep=R:flr=on:fde=none:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:ss=included:st=2.0:spl=backtracking:sp=occurrence_143",
	  "ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_181",
	  "dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_394",
	  "dis-2_20_bs=off:drc=off:ep=R:fde=none:lcm=predicate:nwc=1.3:ptb=off:ssec=off:sos=on:sagn=off:sio=off:spo=on:swb=on_149",
	  "dis-2_20_flr=on:fde=none:lcm=predicate:nwc=1.3:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_510",
	  "dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_71",
	  0
	};
	quickSlices = quick;
      }
    }
    else if (prop == 0) {
      if (atoms <= 70) {
	const char* quick[] = {
	  "ott-1_20_bd=off:bs=off:drc=off:lcm=predicate:nwc=3:sio=off:spl=off:sp=reverse_arity_113",
	  "ott+1_2_bs=unit_only:cond=on:drc=off:gsp=input_only:lcm=predicate:nwc=4:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_75",
	  "lrs+1_3:2_bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=60:sgo=on:spl=backtracking:updr=off_13",
	  "lrs+1011_50_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.5:ptb=off:ssec=off:stl=90:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_68",
	  "ott+1011_128_bs=off:bms=on:drc=off:ep=on:flr=on:fsr=off:lcm=predicate:nwc=5:sswn=on:sgo=on:sio=off:sfv=off:sp=reverse_arity_84",
	  "lrs-1004_32_fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spl=backtracking:sp=occurrence_167",
	  "dis-10_6_bd=off:bs=off:cond=fast:drc=off:gsp=input_only:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_102",
	  "dis+1010_40_bd=off:bms=on:cond=fast:drc=off:ecs=on:ep=on:fde=none:gsp=input_only:nwc=2:ssec=off:sgo=on:urr=on_190",
	  "dis+4_2_bs=off:br=off:cond=on:gs=on:nwc=2.5:sos=on:sac=on:sgo=on:spo=on:urr=on:updr=off_204",
	  "lrs+11_40_bs=off:cond=fast:drc=off:flr=on:fde=none:gsp=input_only:nwc=10:ptb=off:ssec=off:stl=60:spo=on:spl=backtracking:sp=reverse_arity:updr=off_487",
	  "ott+4_64_bd=off:bs=off:drc=off:gs=on:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:spo=on:spl=backtracking_507",
	  "dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_534",
	  0
	};
	quickSlices = quick;
      }
      else {
	const char* quick[] = {
	  "ott+2_32_bd=off:bsr=unit_only:ep=on:flr=on:fde=none:nwc=3:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_68",
	  "ott+1_3_bs=off:bms=on:cond=on:drc=off:ecs=on:fde=none:gsp=input_only:nwc=1.1:ssec=off:sac=on:sgo=on:spo=on_12",
	  "lrs+1011_3_bs=unit_only:bsr=unit_only:cond=on:drc=off:gsp=input_only:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=60:sgo=on:sio=off:spl=backtracking:sfv=off_9",
	  "dis+1003_5_drc=off:ep=on:lcm=reverse:nwc=1:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=reverse_arity:updr=off_66",
	  "dis-1002_128_bsr=unit_only:cond=fast:ep=on:flr=on:nwc=3:sswn=on:sswsr=on:sac=on:sp=occurrence:updr=off_259",
	  "ott+11_14_bd=off:bs=off:bsr=unit_only:drc=off:ep=on:flr=on:fde=none:lcm=predicate:nwc=3:nicw=on:ptb=off:ssec=off:sagn=off:spo=on:spl=backtracking:sp=occurrence:updr=off_208",
	  "ott+4_64_bs=off:cond=on:drc=off:fde=none:gsp=input_only:nwc=4:ptb=off:ssec=off:spl=backtracking_82",
	  "ins+1010_2:3_bs=off:cond=fast:drc=off:gs=on:igbrr=0.8:igrr=1/4:igrp=200:igrpq=2.0:igwr=on:nwc=10:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_305",
	  "lrs-1003_3_bs=unit_only:cond=fast:drc=off:flr=on:fde=none:gs=on:lcm=predicate:nwc=2.5:nicw=on:stl=60:sp=occurrence_311",
	  "dis+10_4_bs=off:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sac=on:sio=off:swb=on_257",
	  "ott+11_7_bs=off:cond=on:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sio=off:spl=backtracking:sp=occurrence:updr=off_579",
	  "ott+1011_40_bd=off:bsr=on:cond=fast:drc=off:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity:updr=off_346",
	  0
	};
	quickSlices = quick;
      }
    }
    else if (prop == 131087) {
      if (atoms > 230000) {
	const char* quick[] = {
	  "dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_50",
	  "dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_46",
	  "dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_161",
	  "ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_49",
	  "lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_23",
	  "ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_31",
	  "ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_44",
	  "dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_98",
	  "dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_20",
	  "dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_19",
	  "lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_37",
	  "dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_91",
	  "dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_46",
	  "dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_82",
	  "ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_213",
	  "ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_123",
	  "dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_93",
	  "lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_119",
	  "ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_155",
	  "lrs+11_20_bd=off:bs=off:drc=off:flr=on:fsr=off:gsp=input_only:gs=on:nwc=1.1:ptb=off:ssec=off:stl=90:sd=2:ss=axioms:st=2.0:sgo=on:spo=on:swb=on_544",
	  "ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_36",
	  "ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_181",
	  0
	};
	quickSlices = quick;
      }
      else if (atoms > 120000) {
	const char* quick[] = {
	  "lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_12",
	  "ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_115",
	  "dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_16",
	  "ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_19",
	  "dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_21",
	  "dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_18",
	  "dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_86",
	  "ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_14",
	  "ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_169",
	  "lrs+10_2_bs=off:br=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=30:sd=1:ss=axioms:st=5.0:sio=off:swb=on:sp=occurrence:urr=on_10",
	  "dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_14",
	  "dis-3_128_bd=off:bsr=unit_only:bms=on:ecs=on:ep=R:fsr=off:fde=none:nwc=1.3:ssec=off:sd=1:ss=included:st=2.0:sos=on:spo=on:sp=reverse_arity_15",
	  "lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:stl=30:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_20",
	  "ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_71",
	  "ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_290",
	  "ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_106",
	  "ott+11_8:1_bs=off:cond=fast:drc=off:fsr=off:fde=none:nwc=4:sd=3:sgt=7:ss=axioms:sos=on:spo=on:sp=reverse_arity:updr=off_150",
	  "dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_172",
	  "dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_194",
	  "lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_882",
	  0
	};
	quickSlices = quick;
      }
      else if (atoms > 40000) {
	const char* quick[] = {
	  "dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_19",
	  "dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_19",
	  "dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_43",
	  "ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_9",
	  "dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_66",
	  "dis-3_128_bd=off:bsr=unit_only:bms=on:ecs=on:ep=R:fsr=off:fde=none:nwc=1.3:ssec=off:sd=1:ss=included:st=2.0:sos=on:spo=on:sp=reverse_arity_6",
	  "dis+1010_64_bd=off:bsr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_27",
	  "lrs+2_4:1_bs=off:br=off:drc=off:ecs=on:gs=on:lcm=reverse:nwc=2.5:ssec=off:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sio=off:sp=reverse_arity:urr=on_10",
	  "lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_8",
	  "dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_7",
	  "dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_89",
	  "dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_15",
	  "ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_181",
	  "lrs-1010_12_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:stl=30:sd=4:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_113",
	  "dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_7",
	  "ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_95",
	  "ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_77",
	  "lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:stl=30:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_134",
	  "lrs+10_3:2_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sd=2:ss=included:sio=off:spl=backtracking_182",
	  "dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_344",
	  "lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_878",
	  "lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:stl=60:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_7",
	  0
	};
	quickSlices = quick;
      }
      else if (atoms > 4000) {
	const char* quick[] = {
	  "dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_9",
	  "lrs+10_2_bs=off:br=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=30:sd=1:ss=axioms:st=5.0:sio=off:swb=on:sp=occurrence:urr=on_3",
	  "dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_16",
	  "lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_8",
	  "dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_70",
	  "dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_36",
	  "ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_61",
	  "ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_73",
	  "ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_22",
	  "dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_53",
	  "dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_2",
	  "lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:stl=30:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_9",
	  "dis-2_5:4_bd=off:bsr=on:cond=fast:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=2:sswsr=on:sos=on:sagn=off:sac=on:spo=on:sp=reverse_arity_4",
	  "dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_4",
	  "dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_9",
	  "dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_23",
	  "ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_7",
	  "dis+1_4_bs=off:bms=on:drc=off:ep=on:fde=none:lcm=reverse:nwc=4:ssec=off:sos=on:sac=on:sp=reverse_arity_69",
	  "dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_94",
	  "ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_86",
	  "ott+11_8:1_bs=off:cond=fast:drc=off:fsr=off:fde=none:nwc=4:sd=3:sgt=7:ss=axioms:sos=on:spo=on:sp=reverse_arity:updr=off_76",
	  "dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_3",
	  "dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_29",
	  "ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_174",
	  "lrs-1010_12_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:stl=30:sd=4:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_277",
	  "lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_779",
	  "lrs+2_4:1_bs=off:br=off:drc=off:ecs=on:gs=on:lcm=reverse:nwc=2.5:ssec=off:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sio=off:sp=reverse_arity:urr=on_17",
	  "dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_135",
	  0
	};
	quickSlices = quick;
      }
      else {
	const char* quick[] = {
	  "ott+1_3_bs=off:bms=on:cond=on:drc=off:ecs=on:fde=none:gsp=input_only:nwc=1.1:ssec=off:sac=on:sgo=on:spo=on_68",
	  "ott+10_8:1_bs=off:bms=on:br=off:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.3:ssec=off:sos=on:sgo=on:sio=off:urr=on_51",
	  "lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_39",
	  "ins+1010_2:3_bs=off:cond=fast:drc=off:gs=on:igbrr=0.8:igrr=1/4:igrp=200:igrpq=2.0:igwr=on:nwc=10:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_6",
	  "dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_100",
	  "dis+1_4_bs=off:bms=on:drc=off:ep=on:fde=none:lcm=reverse:nwc=4:ssec=off:sos=on:sac=on:sp=reverse_arity_2",
	  "dis-1004_50_bs=off:drc=off:ep=R:flr=on:fsr=off:nwc=1.3:ssec=off:sos=on:spo=on:updr=off_44",
	  "dis+1011_1_bd=off:cond=fast:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=2:nicw=on:ptb=off:ssec=off:sgt=7:ss=axioms:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_39",
	  "dis+11_14_bd=off:bs=off:cond=fast:drc=off:ecs=on:nwc=10:ssec=off:sos=on:sagn=off:sac=on:sgo=on:spo=on:sp=reverse_arity_19",
	  "dis-1002_3_bd=off:bs=off:cond=fast:drc=off:ep=R:flr=on:fde=none:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:ss=included:st=2.0:spl=backtracking:sp=occurrence_143",
	  "dis+11_12_bs=unit_only:cond=on:drc=off:ep=RS:flr=on:fsr=off:gsp=input_only:gs=on:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sos=on:sac=on:spo=on:swb=on:sp=reverse_arity:updr=off_22",
	  "ott-1004_2:3_bd=off:bs=off:cond=fast:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=backtracking:sp=occurrence_30",
	  "dis+11_3:2_bs=off:drc=off:ep=R:flr=on:fde=none:nwc=1.7:sos=on:sac=on:sio=off:sp=occurrence_54",
	  "lrs+2_5:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ecs=on:ep=RST:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=5:ssec=off:stl=60:sac=on:sio=off:urr=on_112",
	  "dis+11_2_bs=off:bms=on:drc=off:ecs=on:gsp=input_only:gs=on:lcm=predicate:nwc=2:ssec=off:ss=axioms:sos=on:sio=off:spl=off_78",
	  "dis-2_20_bs=off:drc=off:ep=R:fde=none:lcm=predicate:nwc=1.3:ptb=off:ssec=off:sos=on:sagn=off:sio=off:spo=on:swb=on_149",
	  "dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_394",
	  "dis-2_20_flr=on:fde=none:lcm=predicate:nwc=1.3:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_510",
	  "dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_71",
	  0
	};
	quickSlices = quick;
      }
    }
    else if (prop == 131073) {
      if (atoms > 420) {
	const char* quick[] = {
	  "dis+1011_1_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:swb=on:sp=occurrence_1",
	  "dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_12",
	  "tab+10_1_ep=RST:ss=axioms:spl=off:tbsr=off:tgawr=1/16:tglr=4/1:tipr=off:tlawr=1/50_5",
	  "lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_41",
	  "dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_22",
	  "dis-1002_3_bd=off:bs=off:cond=fast:drc=off:ep=R:flr=on:fde=none:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:ss=included:st=2.0:spl=backtracking:sp=occurrence_107",
	  "dis+1002_8:1_bd=off:bs=unit_only:bsr=on:ep=on:flr=on:nwc=10:sswsr=on:sac=on:sgo=on:sio=off:sfv=off_31",
	  "dis+10_16_bs=off:drc=off:nwc=1.5:nicw=on:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_3",
	  "dis+1011_1_bd=off:bs=off:drc=off:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_60",
	  "ott-1002_28_bd=off:bs=unit_only:bsr=unit_only:ep=on:flr=on:fde=none:lcm=predicate:nwc=5:ptb=off:ssec=off:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_496",
	  "lrs-1010_12_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:stl=30:sd=4:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_108",
	  "lrs+1011_3_bs=unit_only:bsr=unit_only:cond=on:drc=off:gsp=input_only:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=60:sgo=on:sio=off:spl=backtracking:sfv=off_125",
	  "dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_151",
	  "ott+2_3_bs=unit_only:bsr=unit_only:cond=fast:fde=none:gsp=input_only:nwc=1.2:ptb=off:ssec=off:sfv=off:sp=reverse_arity_206",
	  "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_601",
	  "dis+1011_1_bd=off:cond=fast:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=2:nicw=on:ptb=off:ssec=off:sgt=7:ss=axioms:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_1",
	  0
	};
	quickSlices = quick;
      }
      else {
	const char* quick[] = {
	  "dis+10_16_bs=off:drc=off:nwc=1.5:nicw=on:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_11",
	  "ott+10_8:1_bs=off:bms=on:br=off:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.3:ssec=off:sos=on:sgo=on:sio=off:urr=on_11",
	  "ott-1002_28_bd=off:bs=unit_only:bsr=unit_only:ep=on:flr=on:fde=none:lcm=predicate:nwc=5:ptb=off:ssec=off:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_7",
	  "ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_4",
	  "dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_3",
	  "lrs+1_3:2_bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=60:sgo=on:spl=backtracking:updr=off_10",
	  "dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_37",
	  "dis-1010_16_bs=off:bsr=unit_only:drc=off:flr=on:fde=none:lcm=reverse:nwc=1.1:nicw=on:ptb=off:ssec=off:sac=on:spl=backtracking:sp=occurrence:updr=off_80",
	  "ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_1",
	  "lrs+11_40_bs=off:cond=fast:drc=off:flr=on:fde=none:gsp=input_only:nwc=10:ptb=off:ssec=off:stl=60:spo=on:spl=backtracking:sp=reverse_arity:updr=off_59",
	  "dis-1002_128_bsr=unit_only:cond=fast:ep=on:flr=on:nwc=3:sswn=on:sswsr=on:sac=on:sp=occurrence:updr=off_1",
	  "lrs-1010_12_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:stl=30:sd=4:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_4",
	  "dis+1011_1_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:swb=on:sp=occurrence_36",
	  "dis-1010_5_bs=off:drc=off:ep=on:gsp=input_only:gs=on:nwc=2.5:ptb=off:ssec=off:sac=on:sgo=on:sio=off:swb=on:sp=reverse_arity_2",
	  "dis+1011_14_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:nicw=on:sswn=on:sgo=on:spo=on:sp=reverse_arity_29",
	  "dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_7",
	  "ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_46",
	  "dis+11_2_bs=off:bms=on:drc=off:ecs=on:gsp=input_only:gs=on:lcm=predicate:nwc=2:ssec=off:ss=axioms:sos=on:sio=off:spl=off_91",
	  "dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_24",
	  "dis+1010_64_bd=off:bsr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_152",
	  "ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_2",
	  "lrs+1011_3:1_bd=off:flr=on:nwc=10:nicw=on:ptb=off:ssec=off:stl=30:sagn=off:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_69",
	  "dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_151",
	  "lrs+1002_24_bsr=on:cond=on:drc=off:flr=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sswn=on:sswsr=on:stl=30:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity_268",
	  "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_315",
	  "ott+11_14_bd=off:bs=off:bsr=unit_only:drc=off:ep=on:flr=on:fde=none:lcm=predicate:nwc=3:nicw=on:ptb=off:ssec=off:sagn=off:spo=on:spl=backtracking:sp=occurrence:updr=off_101",
	  "dis+10_32_bd=off:bs=off:bsr=on:drc=off:lcm=reverse:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sfv=off:sp=occurrence_115",
	  "lrs+1011_3_bs=unit_only:bsr=unit_only:cond=on:drc=off:gsp=input_only:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=60:sgo=on:sio=off:spl=backtracking:sfv=off_473",
	  "ott+1_2_bs=unit_only:cond=on:drc=off:gsp=input_only:lcm=predicate:nwc=4:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_65",
	  "lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_123",
	  0
	};
	quickSlices = quick;
      }
    }
    else if (prop == 131085 || prop == 131075) {
      const char* quick[] = {
	"dis-1010_1_bs=off:drc=off:fsr=off:gs=on:lcm=predicate:nwc=5:ptb=off:ssec=off:sio=off:spl=off:sp=occurrence_16",
	"dis+10_4_bs=off:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sac=on:sio=off:swb=on_14",
	"dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_12",
	"dis+10_32_bd=off:bs=off:bsr=on:drc=off:lcm=reverse:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sfv=off:sp=occurrence_10",
	"dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_111",
	"dis+11_14_bd=off:bs=off:cond=fast:drc=off:ecs=on:nwc=10:ssec=off:sos=on:sagn=off:sac=on:sgo=on:spo=on:sp=reverse_arity_9",
	"ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_36",
	"dis+1002_8:1_bd=off:bs=unit_only:bsr=on:ep=on:flr=on:nwc=10:sswsr=on:sac=on:sgo=on:sio=off:sfv=off_22",
	"dis+1011_64_bd=off:bs=unit_only:bsr=unit_only:drc=off:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=5:ptb=off:ssec=off:sos=on:sagn=off:sgo=on:spl=backtracking:sp=occurrence_67",
	"dis+1011_14_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:nicw=on:sswn=on:sgo=on:spo=on:sp=reverse_arity_241",
	"ott-1002_28_bd=off:bs=unit_only:bsr=unit_only:ep=on:flr=on:fde=none:lcm=predicate:nwc=5:ptb=off:ssec=off:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_122",
	"ott+1_3_bs=off:bms=on:cond=on:drc=off:ecs=on:fde=none:gsp=input_only:nwc=1.1:ssec=off:sac=on:sgo=on:spo=on_208",
	"dis-2_20_flr=on:fde=none:lcm=predicate:nwc=1.3:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_220",
	"lrs+10_3:2_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sd=2:ss=included:sio=off:spl=backtracking_509",
	"ott+11_7_bs=off:cond=on:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sio=off:spl=backtracking:sp=occurrence:updr=off_567",
	0
      };
      quickSlices = quick;    
    }
    else if (prop == 131072) {
      const char* quick[] = {
	"dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_1",
	"dis+1002_8:1_bd=off:bs=unit_only:bsr=on:ep=on:flr=on:nwc=10:sswsr=on:sac=on:sgo=on:sio=off:sfv=off_3",
	"lrs+1011_3:1_bd=off:flr=on:nwc=10:nicw=on:ptb=off:ssec=off:stl=30:sagn=off:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_1",
	"dis+1011_1_bd=off:bs=off:drc=off:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_11",
	"dis-1010_7_bd=off:br=off:cond=fast:drc=off:gsp=input_only:gs=on:lcm=predicate:nwc=1:ptb=off:ssec=off:spl=backtracking:sp=occurrence:urr=on_1",
	"ott-1004_2:3_bd=off:bs=off:cond=fast:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=backtracking:sp=occurrence_9",
	"ott+1_2_bs=unit_only:cond=on:drc=off:gsp=input_only:lcm=predicate:nwc=4:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_20",
	"lrs-1010_10_bd=off:bs=unit_only:cond=on:flr=on:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_3",
	"dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_18",
	"dis+1003_128_bs=off:drc=off:ecs=on:fsr=off:lcm=reverse:nwc=2.5:ssec=off:sos=on:sac=on:sgo=on:spo=on:sp=occurrence_39",
	"ott+11_128_fsr=off:fde=none:lcm=reverse:nwc=1:ptb=off:ssec=off:sio=off:spo=on:swb=on:sfv=off:sp=reverse_arity_562",
	"lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:stl=120:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_192",
	"dis+10_16_bs=off:drc=off:nwc=1.5:nicw=on:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_291",
	"lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_546",
	"dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_1",
	"lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:stl=30:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_2",
	"ins+1010_2:3_bs=off:cond=fast:drc=off:gs=on:igbrr=0.8:igrr=1/4:igrp=200:igrpq=2.0:igwr=on:nwc=10:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_35",
	0
      };
      quickSlices = quick;
    }
    else {
      const char* quick[] = {
	"ins+1010_2:3_bs=off:cond=fast:drc=off:gs=on:igbrr=0.8:igrr=1/4:igrp=200:igrpq=2.0:igwr=on:nwc=10:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_3",
	"dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_6",
	"ott-1002_28_bd=off:bs=unit_only:bsr=unit_only:ep=on:flr=on:fde=none:lcm=predicate:nwc=5:ptb=off:ssec=off:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_21",
	"dis+1011_1_bd=off:bs=off:drc=off:lcm=predicate:nwc=4:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_2",
	"lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:stl=30:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_2",
	"lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:stl=30:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_34",
	"dis+1010_64_bd=off:bsr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_2",
	"dis+1011_14_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:nicw=on:sswn=on:sgo=on:spo=on:sp=reverse_arity_111",
	"dis+10_16_bs=off:drc=off:nwc=1.5:nicw=on:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_1",
	"ott+11_7_bs=off:cond=on:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sio=off:spl=backtracking:sp=occurrence:updr=off_2",
	"ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_62",
	"ott+1011_3:1_bs=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sswsr=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_37",
	"ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_20",
	"dis-2_5:4_bd=off:bsr=on:cond=fast:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=2:sswsr=on:sos=on:sagn=off:sac=on:spo=on:sp=reverse_arity_1",
	"dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_107",
	"dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_76",
	"dis+1011_64_bd=off:bs=unit_only:bsr=unit_only:drc=off:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=5:ptb=off:ssec=off:sos=on:sagn=off:sgo=on:spl=backtracking:sp=occurrence_21",
	"dis+11_14_bd=off:bs=off:cond=fast:drc=off:ecs=on:nwc=10:ssec=off:sos=on:sagn=off:sac=on:sgo=on:spo=on:sp=reverse_arity_3",
	"lrs+10_3:2_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:stl=60:sd=2:ss=included:sio=off:spl=backtracking_80",
	"ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_6",
	"dis+3_20_bd=off:bs=off:drc=off:fsr=off:fde=none:gsp=input_only:gs=on:nwc=1.2:nicw=on:ssec=off:sos=on:sac=on:sgo=on:spo=on_50",
	"dis+10_32_bd=off:bs=off:bsr=on:drc=off:lcm=reverse:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sfv=off:sp=occurrence_28",
	"dis-2_20_flr=on:fde=none:lcm=predicate:nwc=1.3:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_121",
	"ott+1010_8:1_bs=off:cond=fast:drc=off:nwc=4:ptb=off:ssec=off:sac=on:spl=backtracking:sfv=off:sp=reverse_arity_277",
	"lrs+11_20_bd=off:bs=off:drc=off:flr=on:fsr=off:gsp=input_only:gs=on:nwc=1.1:ptb=off:ssec=off:stl=90:sd=2:ss=axioms:st=2.0:sgo=on:spo=on:swb=on_322",
	"lrs-1003_3_bs=unit_only:cond=fast:drc=off:flr=on:fde=none:gs=on:lcm=predicate:nwc=2.5:nicw=on:stl=60:sp=occurrence_301",
	"lrs+1_3:1_bd=off:bs=off:bsr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:stl=30:sos=on:sac=on:sio=off:spo=on:spl=backtracking_153",
	"lrs+1002_24_bsr=on:cond=on:drc=off:flr=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sswn=on:sswsr=on:stl=30:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity_15",
	"dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_30",
	0
      };
      quickSlices = quick;
    }
    break;
  }

  case Property::FNE: {
    if (atoms > 2000) {
      const char* quick[] = {
	"dis-1002_5:1_bs=unit_only:bsr=unit_only:flr=on:gsp=input_only:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sswn=on:sos=on:spo=on:swb=on:sp=occurrence_15",
	"dis+1011_1_bs=off:cond=fast:gs=on:lcm=predicate:nwc=4:ptb=off:ssec=off:sos=on:sac=on:sgo=on:spo=on:swb=on:sp=reverse_arity_152",
	"dis+1002_24_bs=off:cond=on:ecs=on:lcm=reverse:ssec=off:spo=on:sp=reverse_arity:updr=off_110",
	"ott+11_32_bsr=on:cond=on:flr=on:fsr=off:gsp=input_only:lcm=reverse:nwc=5:nicw=on:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking:updr=off_130",
	"dis+1011_128_bsr=on:bms=on:cond=on:fsr=off:lcm=reverse:nwc=4:nicw=on:sswn=on:sswsr=on:sac=on:sio=off:sp=occurrence:updr=off_593",
	"dis-10_8:1_bs=off:cond=fast:gsp=input_only:gs=on:nwc=5:ptb=off:ssec=off:sos=on:spl=backtracking:sp=occurrence_577",
	0
      };
      quickSlices = quick;
    }
    else {
      const char* quick[] = {
	"dis+10_128_bs=off:cond=fast:gsp=input_only:gs=on:lcm=predicate:nwc=1.1:ptb=off:ssec=off:spo=on:swb=on:sp=reverse_arity:urr=on_4",
	"ott+1010_64_bs=off:flr=on:gsp=input_only:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:sagn=off:sgo=on:sio=off:spo=on:spl=backtracking:updr=off_157",
	"dis+1011_128_bsr=on:bms=on:cond=on:fsr=off:lcm=reverse:nwc=4:nicw=on:sswn=on:sswsr=on:sac=on:sio=off:sp=occurrence:updr=off_18",
	"dis+4_10_bs=off:ep=on:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_8",
	"dis+1011_2_bs=off:flr=on:gsp=input_only:gs=on:lcm=predicate:nwc=1:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spo=on:swb=on:sp=occurrence:updr=off_19",
	"dis+4_128_bs=off:cond=fast:gs=on:lcm=predicate:nwc=5:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spo=on:swb=on:sp=occurrence:updr=off_4",
	"dis+2_5:4_bs=off:bms=on:cond=fast:fsr=off:lcm=reverse:nwc=1:ssec=off:sgo=on:sio=off:sp=reverse_arity_11",
	"dis+1003_8_bms=on:ecs=on:lcm=predicate:nwc=3.0:ssec=off:sgo=on:sio=off:spo=on:sp=occurrence:updr=off_39",
	"lrs+11_3:2_bs=unit_only:bsr=unit_only:cond=on:fsr=off:lcm=predicate:nwc=1.3:ptb=off:ssec=off:stl=60:sac=on:spl=backtracking_28",
	"dis-1002_3_bs=off:bsr=unit_only:gsp=input_only:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:swb=on:sp=occurrence:urr=on:updr=off_168",
	"ott+10_4_bs=off:bms=on:cond=fast:gsp=input_only:gs=on:lcm=reverse:nwc=5:nicw=on:ssec=off:sgo=on:sp=occurrence:urr=on_140",
	"dis+10_24_bsr=unit_only:cond=fast:nwc=10:ptb=off:ssec=off:sgo=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity:updr=off_316",
	"dis+1004_7_bs=off:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sos=on:sagn=off:spo=on:spl=backtracking:updr=off_732",
	"dis+2_28_bs=off:lcm=reverse:nwc=1:nicw=on:sswn=on:sswsr=on:sac=on:sgo=on:spo=on:sp=reverse_arity:updr=off_5",
	"tab+10_1_gsp=input_only:spl=off:tbsr=off:tfsr=off:tgawr=1/128:tglr=1/7:tipr=off:tlawr=1/2_179",
	0
      };
      quickSlices = quick;
    }
    break;
  }

  case Property::EPR: {
    if (atoms > 2000) {
      const char* quick[] = {
	"dis-1_128_bs=off:bsr=on:bms=on:fde=none:lcm=predicate:nwc=1:ssec=off:sac=on:urr=on_46",
	"ins+2_12_bs=off:flr=on:gs=on:igbrr=1.0:igrr=1/64:igrp=400:igrpq=1.0:igwr=on:nwc=2:ptb=off:ssec=off:spl=off:sp=reverse_arity_46",
	"ott+1_64_bs=off:cond=on:lcm=predicate:nwc=1.1:sgo=on:spo=on:sp=occurrence:urr=on_232",
	"ins+3_5:4_bsr=unit_only:cond=on:flr=on:gsp=input_only:igbrr=0.3:igrpq=1.5:nwc=3:ptb=off:ssec=off:spl=off:sp=reverse_arity_2103",
	0
      };
      quickSlices = quick;
    }
    else if (atoms > 1250) {
      const char* quick[] = {
	"dis-11_20_bs=off:fde=none:gsp=input_only:gs=on:nwc=3:ptb=off:ssec=off:sac=on:swb=on:sp=occurrence_2",
	"ott+10_50_bd=off:bs=off:bsr=unit_only:fde=none:gs=on:lcm=predicate:nwc=1:nicw=on:sac=on:sio=off:urr=on_310",
	"ins+10_24_bd=off:bs=off:br=off:drc=off:flr=on:fde=none:gsp=input_only:gs=on:igbrr=0.7:igrr=1/4:igrp=700:igrpq=2.0:igwr=on:lcm=reverse:nwc=1.1:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_300",
	"ins+2_50_bd=off:bs=off:br=off:cond=on:drc=off:ep=R:fde=none:gsp=input_only:gs=on:igbrr=0.8:igrr=1/2:igrp=700:igrpq=2.0:igwr=on:lcm=predicate:nwc=1.3:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_466",
	"ins+2_64_bd=off:bs=off:br=off:cond=on:drc=off:igbrr=0.4:igrr=16/1:igrp=2000:igrpq=1.1:igwr=on:nwc=1.3:ptb=off:ssec=off:spl=off:sp=occurrence:urr=on_766",
	"ins-11_10_bs=off:cond=on:fsr=off:gsp=input_only:igbrr=0.8:igrr=1/128:igrp=400:igrpq=1.2:igwr=on:lcm=reverse:nwc=10:ptb=off:ssec=off:spl=off:sp=occurrence_1",
	0
      };
      quickSlices = quick;
    }
    else if (atoms > 900) {
      const char* quick[] = {
	"ins+1_40_bs=off:fde=none:gsp=input_only:igbrr=0.8:igrr=16/1:igrp=200:igrpq=2.0:igwr=on:nwc=1.7:ptb=off:ssec=off:spl=off_16",
	"dis-1_128_bs=off:bsr=on:bms=on:fde=none:lcm=predicate:nwc=1:ssec=off:sac=on:urr=on_28",
	"ott+10_50_bd=off:bs=off:bsr=unit_only:fde=none:gs=on:lcm=predicate:nwc=1:nicw=on:sac=on:sio=off:urr=on_566",
	"ins+4_50_bd=off:bs=off:br=off:cond=fast:drc=off:fsr=off:fde=none:gsp=input_only:gs=on:igbrr=0.6:igrr=1/64:igrp=200:igrpq=1.5:igwr=on:nwc=4:ptb=off:ssec=off:spl=off:sp=occurrence:urr=on_661",
	"ins-1010_2:3_bs=unit_only:cond=on:flr=on:fsr=off:gsp=input_only:gs=on:igbrr=0.9:igrp=100:igrpq=1.3:lcm=reverse:nwc=1.1:ptb=off:ssec=off:spl=off:sp=reverse_arity:updr=off_2148",
	0
      };
      quickSlices = quick;
    }
    else {
      const char* quick[] = {
	"ins+1_40_bs=off:fde=none:gsp=input_only:igbrr=0.8:igrr=16/1:igrp=200:igrpq=2.0:igwr=on:nwc=1.7:ptb=off:ssec=off:spl=off_21",
	"ins-1002_16_bs=off:cond=on:drc=off:flr=on:fde=none:gs=on:igbrr=0.3:igrr=1/8:igrp=200:igrpq=2.0:igwr=on:lcm=predicate:nwc=1.2:ptb=off:ssec=off:spl=off:urr=on_5",
	"dis-1_128_bs=off:bsr=on:bms=on:fde=none:lcm=predicate:nwc=1:ssec=off:sac=on:urr=on_20",
	"ins+3_5_bs=off:flr=on:gsp=input_only:igbrr=0.1:igrr=1/32:igrp=700:igrpq=2.0:igwr=on:lcm=predicate:nwc=1:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_37",
	"ins+1_4_bd=off:bs=off:bsr=on:cond=on:drc=off:ep=RS:fde=none:gs=on:igbrr=0.6:igrr=1/16:igrp=2000:igrpq=2.0:igwr=on:lcm=predicate:nwc=1.7:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_177",
	"ott+11_50_bd=off:bs=off:cond=on:ecs=on:fde=none:gsp=input_only:lcm=predicate:nwc=4:nicw=on:ssec=off_1847",
	0
      };
      quickSlices = quick;
    }
    break;
  }
  case Property::UEQ: {
    if (prop == 0) {
      if (atoms > 14) {
	const char* quick[] = {
	  "lrs+10_14_bs=unit_only:drc=off:nwc=1.2:stl=180:sp=reverse_arity_30",
	  "lrs+10_5:1_bs=off:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.1:stl=60_331",
	  "dis+10_128_bs=unit_only:drc=off:fsr=off:fde=none:gsp=input_only:nwc=10_295",
	  "ott+10_4_bs=off:fde=none:nwc=1.3_1358",
	  "dis+10_2:1_bsr=unit_only:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.5:sp=occurrence_1043",
	  0
	};
	quickSlices = quick;
      }
      else if (atoms > 10) {
	const char* quick[] = {
	  "lrs+10_12_bs=off:bsr=unit_only:drc=off:nwc=1.7:stl=180_899",
	  "lrs+10_16_bs=unit_only:bsr=unit_only:drc=off:nwc=1.2:stl=60:sp=occurrence_486",
	  0
	};
	quickSlices = quick;
      }
      else if (atoms > 9) {
	const char* quick[] = {
	  "lrs+10_2:3_bs=unit_only:bsr=unit_only:drc=off:fde=none:nwc=1.7:stl=90:sp=occurrence_301",
	  "lrs+10_5:4_bs=off:flr=on:nwc=5.0:stl=60:sp=occurrence_96",
	  "ott+10_4_bs=unit_only:bsr=unit_only:drc=off:nwc=1.7_603",
	  "ott+10_2:1_bsr=unit_only:drc=off:fsr=off:fde=none:nwc=4:sp=occurrence_973",
	  "ott+10_4_bs=off:fde=none:nwc=1.3_1485",
	  "ott+10_2:3_bs=off:drc=off:fsr=off:nwc=1.2:sp=occurrence_1348",
	  0
	};
	quickSlices = quick;
      }
      else {
	const char* quick[] = {
	  "ott+10_64_bd=off:bs=unit_only:drc=off:fsr=off:nwc=1.1:sp=occurrence_15",
	  "lrs+10_14_bs=unit_only:drc=off:nwc=1.2:stl=180:sp=reverse_arity_1094",
	  "ott+10_5_bd=off:bs=unit_only:drc=off:fsr=off:nwc=4:sp=occurrence_702",
	  "ott+10_4_bs=unit_only:bsr=unit_only:drc=off:nwc=1.7_744",
	  0
	};
	quickSlices = quick;
      }
    }
    else if (prop == 2) {
      if (atoms > 15) {
	const char* quick[] = {
	  "lrs+10_2:3_bs=unit_only:bsr=unit_only:drc=off:fde=none:nwc=1.7:stl=90:sp=occurrence_3",
	  "lrs+10_5:4_bs=off:flr=on:nwc=5.0:stl=60:sp=occurrence_5",
	  "ott+10_6_bs=off:drc=off:fsr=off:fde=none:nwc=1.2_135",
	  "ott+10_8_bd=off:bs=off:drc=off:fsr=off:fde=none:nwc=2:sp=occurrence_43",
	  "ott+10_3_bs=off:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.3:sp=occurrence_208",
	  "dis+10_5_bs=off:drc=off:fsr=off:gsp=input_only:nwc=5:sp=reverse_arity_392",
	  "dis+10_6_bd=off:bs=off:drc=off:gs=on:nwc=1.1:sp=occurrence_185",
	  "ott+10_128_bs=off:bsr=unit_only:drc=off:fsr=off:nwc=1.1_984",
	  0
	};
	quickSlices = quick;
      }
      else {
	const char* quick[] = {
	  "lrs+10_20_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.3:stl=60:sp=occurrence_195",
	  "ott+10_32_bs=unit_only:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.1_192",
	  "lrs+10_28_bs=off:drc=off:nwc=10:stl=30:sp=occurrence_146",
	  "lrs+10_5:4_bs=off:flr=on:nwc=5.0:stl=60:sp=occurrence_146",
	  "lrs+10_14_bs=unit_only:drc=off:nwc=1.2:stl=180:sp=reverse_arity_410",
	  "ott+10_50_bs=off:drc=off:nwc=10_854",
	  0
	};
	quickSlices = quick;
      }
    }
    else {
      const char* quick[] = {
	"dis+10_28_bs=unit_only:bsr=on:drc=off:fsr=off:fde=none:nwc=2.5:sp=reverse_arity_10",
	"dis+10_2_bs=off:gs=on:nwc=1:sp=reverse_arity_29",
	"ott+10_64_bd=off:bs=unit_only:drc=off:fsr=off:nwc=1.1:sp=occurrence_32",
	"dis+10_128_bs=unit_only:drc=off:fsr=off:fde=none:gsp=input_only:nwc=10_149",
	"lrs+10_128_bd=off:bs=unit_only:drc=off:gsp=input_only:nwc=1.3:stl=60:sp=occurrence_84",
	"lrs+10_8:1_bs=unit_only:drc=off:gsp=input_only:nwc=2.5:stl=30:sp=reverse_arity_207",
	0
      };
      quickSlices = quick;
    }
    break;
  }
  }

  switch (cat) {
  case Property::NEQ:
    {
      const char* fallback[] = {
        "dis+10_5_bs=off:cond=on:flr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sp=occurrence_600",
        "dis+1011_7_cond=on:drc=off:ecs=on:ep=on:gs=on:lcm=predicate:nwc=1.7:ssec=off:sos=on:sac=on:sgo=on:sp=reverse_arity_300",
        "dis+1010_6_bd=off:nwc=10.0:ssec=off:sac=on:sp=occurrence_600",
        "ott+11_2_bd=off:bs=off:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:spo=on:spl=backtracking:sp=reverse_arity_300",
        "dis+1011_50_bs=unit_only:gsp=input_only:lcm=reverse:nwc=1.7:ptb=off:ssec=off:sac=on:spo=on:spl=backtracking:updr=off_600",
        "dis+11_40_bsr=unit_only:cond=fast:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:spl=backtracking:sfv=off_600",
        "dis+11_6_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1:ptb=off:ssec=off:sos=on:sgo=on:sio=off:swb=on:sp=occurrence:updr=off_600",
        "ott+1011_3_bs=off:drc=off:ep=on:fde=none:gsp=input_only:nwc=1:sgo=on:sio=off:spo=on:updr=off_300",
        "dis-1002_3:2_bs=off:cond=on:drc=off:ep=RS:flr=on:lcm=predicate:nwc=10:ssec=off:sgo=on:sio=off:spo=on:sp=reverse_arity_300",
        "dis+1010_2:3_bs=off:drc=off:ep=on:nwc=10:ssec=off:sos=on:sgo=on:sio=off:sp=occurrence_300",
        "dis+1011_14_bd=off:bs=off:bsr=on:cond=fast:ep=on:gsp=input_only:lcm=reverse:nwc=2:sswn=on:sswsr=on:sac=on:sgo=on:spo=on:sfv=off:sp=reverse_arity:updr=off_300",
        "dis+11_12_bs=unit_only:cond=on:flr=on:fde=none:lcm=reverse:nwc=1.5:sswn=on:sswsr=on:sgo=on:sfv=off:sp=reverse_arity_900",
        "dis-1002_8:1_bs=off:br=off:drc=off:ecs=on:ep=on:fde=none:gs=on:nwc=1.2:nicw=on:ssec=off:sd=5:ss=axioms:st=1.2:sos=on:sac=on:sio=off:sp=reverse_arity:urr=on_300",
        "dis+4_10_bd=off:bs=off:cond=fast:fde=none:nwc=10.0:ptb=off:ssec=off:sgo=on:spl=backtracking:sp=reverse_arity_600",
        "dis+2_8:1_bs=off:br=off:cond=fast:drc=off:ep=RST:flr=on:fsr=off:fde=none:gsp=input_only:nwc=1.1:ssec=off:sac=on:spo=on:sp=reverse_arity:urr=on_300",
        "lrs-1010_12_bd=off:gsp=input_only:nwc=3.0:ptb=off:ssec=off:sos=on:sagn=off:sac=on:spl=backtracking:sp=reverse_arity:updr=off_600",
        "lrs+1011_20_bd=off:bs=off:bsr=on:cond=on:drc=off:fsr=off:gs=on:lcm=reverse:nwc=3:ssec=off:sos=on:sagn=off:sio=off:spl=off_300",
        "ott+1011_2:3_bs=off:bsr=unit_only:ep=on:gsp=input_only:nwc=3:sac=on:sgo=on:spo=on:sfv=off_300",
        "lrs-4_1_bd=off:bs=off:bms=on:ecs=on:gsp=input_only:nicw=on:ssec=off:sos=on:sio=off:spl=off_600",
        "lrs+11_20_bs=off:cond=on:drc=off:flr=on:fsr=off:gs=on:nwc=2.5:ssec=off:sgo=on:spo=on:sp=reverse_arity:urr=on:updr=off_600",
        "lrs+1_4:1_bd=off:bs=off:cond=on:fde=none:lcm=predicate:sos=on_600",
        "ott+11_28_bs=off:cond=on:drc=off:ecs=on:fde=none:gs=on:nwc=1.7:ssec=off:sgo=on:sio=off:sp=reverse_arity_300",
        "dis+10_128_bs=off:cond=on:drc=off:flr=on:fsr=off:fde=none:lcm=predicate:nwc=2:ptb=off:ssec=off:sac=on:swb=on_300",
        "dis+1010_2:1_bs=off:drc=off:ep=RS:fsr=off:fde=none:gsp=input_only:nwc=10:ssec=off:sio=off:sp=reverse_arity_300",
        "dis+3_14_bs=off:drc=off:ecs=on:fde=none:gsp=input_only:nwc=1.2:nicw=on:ssec=off:sac=on:sio=off:sp=occurrence:urr=on_300",
        "dis-1004_8:1_bs=off:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=10:nicw=on:ssec=off:sp=reverse_arity_300",
        "ott+11_3_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:fde=none:nwc=10:ptb=off:ssec=off:sac=on:spo=on:spl=backtracking:sfv=off:updr=off_300",
        "lrs+4_4_bd=off:cond=on:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:spl=backtracking:sp=reverse_arity_300",
        "dis+11_40_bd=off:bs=off:cond=fast:ep=on:flr=on:gsp=input_only:gs=on:lcm=reverse:nwc=5:ptb=off:ssec=off:sac=on:sio=off:swb=on:sfv=off_300",
        "dis+1011_10_bd=off:bs=unit_only:bsr=on:bms=on:cond=fast:ep=on:lcm=predicate:nwc=1:nicw=on:ssec=off:sac=on:sgo=on:sio=off:spo=on:sfv=off:sp=occurrence:updr=off_300",
        "dis-1010_5:1_bs=off:cond=fast:ep=R:lcm=reverse:nwc=1.2:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:sfv=off:sp=occurrence_300",
        "ott+10_64_bd=off:bsr=unit_only:bms=on:fde=none:nwc=1.5:sswn=on:sswsr=on:sac=on:sgo=on:sio=off:spo=on:sfv=off:updr=off_300",
        "ott-1010_5:4_bd=off:bs=off:bms=on:cond=on:drc=off:ep=on:lcm=predicate:nwc=1:nicw=on:ssec=off:sd=3:ss=axioms:sos=on:sio=off:sp=reverse_arity:urr=on_300",
        "ott+11_5:1_bs=off:cond=fast:drc=off:ep=on:fsr=off:gsp=input_only:nwc=4:nicw=on:sswn=on:sac=on:sgo=on:sp=occurrence_900",
        "dis+11_5:1_cond=fast:ep=on:gsp=input_only:nwc=10:sswn=on:sswsr=on_600",
        "ott+10_50_bd=off:bms=on:cond=on:drc=off:flr=on:fde=none:gs=on:lcm=predicate:nwc=2.5:nicw=on:sswn=on:sos=on:sac=on:sio=off:spo=on:sp=occurrence:updr=off_300",
        "ott+11_3_bs=unit_only:bsr=unit_only:cond=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.1:ptb=off:ssec=off:sac=on:sgo=on:spo=on:spl=backtracking:sfv=off:sp=occurrence:updr=off_300",
        "dis+1002_10_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_600",
        "ott+1_2:1_bd=off:bs=off:bms=on:cond=fast:ep=on:flr=on:fsr=off:nwc=5:spo=on:sfv=off:sp=reverse_arity:updr=off_300",
        "ott-1010_128_bd=off:bs=off:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=1:nicw=on:sswn=on:sswsr=on:sos=on:sac=on:sfv=off:sp=reverse_arity:updr=off_300",
        "dis+1_50_cond=fast:lcm=predicate:nwc=3.0_600",
        "dis+11_1_bsr=unit_only:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sswsr=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence:updr=off_1800",
        "dis+1010_4:1_bs=off:bsr=unit_only:cond=on:ep=RS:gs=on:lcm=reverse:nwc=4:sswn=on:sos=on:spo=on:sp=occurrence_300",
        "lrs-1010_64_bd=off:bs=off:drc=off:nwc=2:ssec=off:sac=on:sgo=on:spo=on_300",
        "lrs+2_2_bd=off:bs=unit_only:bsr=unit_only:cond=fast:drc=off:flr=on:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sac=on:sgo=on:sio=off:swb=on_600",
        "lrs+1004_14_bd=off:cond=on:drc=off:ep=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=3:sswsr=on:sio=off:spl=off:updr=off_300",
        "dis+1_5:1_bd=off:bs=unit_only:cond=fast:drc=off:flr=on:fde=none:lcm=reverse:nwc=10:ptb=off:ssec=off:sio=off:spo=on:swb=on_300",
        "lrs+1002_2:1_bd=off:bs=unit_only:bsr=on:cond=on:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=4:ptb=off:ssec=off:sac=on:sio=off:sp=occurrence_600",
        "dis+1_2:1_drc=off:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sio=off:spl=backtracking:sp=reverse_arity:updr=off_600",
        "dis+10_8_bs=off:cond=on:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_600",
        0
      };
      fallbackSlices = fallback;
    }
    break;

  case Property::HEQ:
  case Property::PEQ:
    {
      const char* fallback[] = {
        "lrs+10_2_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=10.0:ptb=off:ssec=off:sgo=on:sio=off:swb=on:sp=reverse_arity:updr=off_600",
        "ott+1011_20_bsr=on:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.1:nicw=on:ptb=off:ssec=off:sagn=off:sac=on:sgo=on:spo=on:spl=backtracking:sp=reverse_arity_1800",
        "ott+1011_50_bs=off:bsr=on:cond=fast:drc=off:fsr=off:fde=none:lcm=predicate:nwc=1.3:sswsr=on:sgo=on:sfv=off:sp=occurrence_1500",
        "lrs-4_2_bs=off:bms=on:cond=fast:drc=off:fde=none:gsp=input_only:nwc=1.2:nicw=on:sac=on:sio=off:spo=on:sfv=off_600",
        "dis+2_128_bs=off:drc=off:lcm=predicate:nwc=10:sac=on:sio=off:sp=occurrence_300",
        "dis+1003_28_bsr=on:drc=off:flr=on:fsr=off:fde=none:gsp=input_only:nwc=1.3:sos=on:sfv=off_600",
        "dis+10_2_bd=off:cond=on:ecs=on:flr=on:gsp=input_only:nwc=5.0:nicw=on:ssec=off:sio=off:spl=off:sp=occurrence:updr=off_900",
        "lrs+1010_8_cond=on:flr=on:nwc=1:sswn=on:sswsr=on:sac=on:sgo=on:spo=on:updr=off_600",
        "dis+2_10_bd=off:bs=unit_only:bsr=unit_only:ep=RS:fsr=off:lcm=reverse:nwc=1.7:nicw=on:ptb=off:ssec=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_600",
        "dis+4_28_bd=off:bs=off:cond=on:drc=off:nwc=4:ptb=off:ssec=off:sos=on:sac=on:sio=off:swb=on_300",
        "lrs-11_1_bd=off:bs=off:cond=fast:drc=off:flr=on:lcm=predicate:nwc=2:nicw=on:spo=on:sp=occurrence_300",
        "dis+1004_128_cond=on:ep=on:flr=on:gsp=input_only:nwc=3.0:updr=off_600",
        "ott+1004_2_bd=off:bsr=on:drc=off:ep=on:fsr=off:gsp=input_only:nwc=1.5:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spl=backtracking:sfv=off_900",
        "lrs+4_4_bd=off:bsr=unit_only:bms=on:cond=on:drc=off:ecs=on:flr=on:fsr=off:fde=none:gsp=input_only:nwc=5:nicw=on:ssec=off:sac=on:sio=off:spo=on:sfv=off_600",
        "lrs+10_5_bsr=on:drc=off:ep=on:gsp=input_only:nwc=1.2:sos=on:updr=off_600",
        "dis-1_10_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:flr=on:fsr=off:nwc=1.2:sswn=on:sagn=off:spo=on:sfv=off_600",
        "lrs+2_1_bms=on:cond=on:ecs=on:flr=on:gsp=input_only:lcm=predicate:nicw=on:ssec=off:sos=on:sac=on:sgo=on:spo=on:sp=reverse_arity_600",
        "ins+11_24_bd=off:bs=off:cond=fast:drc=off:fde=none:igbrr=0.0:igrr=1/32:igrp=100:igrpq=1.2:igwr=on:nwc=3:ptb=off:ssec=off:spl=off_300",
        "lrs+1010_5_bd=off:bs=off:bms=on:fde=none:gsp=input_only:nwc=2.5:nicw=on:sswsr=on:sgo=on:sio=off:sp=reverse_arity:updr=off_600",
        "lrs-1_32_bd=off:bs=off:bsr=on:cond=on:ecs=on:gsp=input_only:lcm=predicate:nwc=4:nicw=on:ssec=off:sac=on:sio=off:spo=on:sp=occurrence_600",
        "dis+1004_2_bd=off:bs=off:bsr=unit_only:cond=on:drc=off:flr=on:fsr=off:gsp=input_only:nwc=1.5:sswsr=on:sac=on:sio=off:spo=on:sfv=off_600",
        "ott+2_28_bs=off:bms=on:drc=off:ecs=on:fde=none:gsp=input_only:nwc=1.1:ssec=off:sio=off:spl=off_300",
        "lrs+11_5:4_bs=off:bsr=unit_only:bms=on:cond=fast:flr=on:nwc=2.5:nicw=on:sio=off_600",
        "ott+1003_4_bd=off:bms=on:cond=fast:drc=off:ep=on:flr=on:fsr=off:nwc=1.3:sswn=on:sac=on:sgo=on:sio=off:spo=on:sfv=off:sp=reverse_arity:updr=off_900",
        "ott+1011_128_bs=off:bsr=on:cond=on:drc=off:ep=on:flr=on:fsr=off:nwc=1:nicw=on:ssec=off:sagn=off:sac=on:sio=off:sfv=off:sp=occurrence:updr=off_1800",
        "dis+2_40_bd=off:bs=off:cond=fast:fsr=off:gsp=input_only:nwc=4.0:ptb=off:ssec=off:sagn=off:sgo=on:sio=off:spl=backtracking:sp=reverse_arity_900",
        "dis-11_32_bd=off:bs=unit_only:cond=on:drc=off:fsr=off:fde=none:nwc=1.5:ptb=off:ssec=off:sac=on:sgo=on:spo=on:swb=on:sfv=off:sp=occurrence_900",
        "lrs-10_12_bd=off:bs=off:bms=on:cond=on:drc=off:ep=on:gsp=input_only:nwc=1.5:nicw=on:sswn=on:sswsr=on:sfv=off_600",
        "ott+4_128_bs=off:bms=on:cond=on:drc=off:fsr=off:nwc=1.1:ssec=off:sagn=off:sac=on:sgo=on:sio=off:spo=on:sfv=off_600",
        "ott+1011_7_bs=off:drc=off:fde=none:gsp=input_only:nwc=2.5:ptb=off:ssec=off:sio=off:swb=on:sp=occurrence_600",
        "ott-1004_50_bs=off:bsr=unit_only:bms=on:drc=off:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:sswsr=on:sfv=off:updr=off_900",
        "ott+2_3:2_bd=off:bs=unit_only:bsr=unit_only:cond=on:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:nwc=5:sswn=on:sgo=on:sio=off:sp=reverse_arity_900",
        0
      };
      fallbackSlices = fallback;
    }
    break;

  case Property::HNE: 
  case Property::NNE: 
    {
      const char* fallback[] = {
        "lrs+11_12_fsr=off:nwc=3:sgo=on:sio=off:sp=reverse_arity_600",
        "dis+1010_20_lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_600",
        "dis+1011_128_bs=off:gsp=input_only:nwc=1.7:nicw=on:sswsr=on:sos=on:spo=on:sp=reverse_arity_300",
        "dis+1011_20_bs=off:fsr=off:nwc=2:ssec=off:sio=off:spl=off:sp=occurrence_300",
        "dis+11_128_bs=off:cond=fast:flr=on:lcm=reverse:nwc=2:ptb=off:ssec=off:sac=on:updr=off_300",
        "dis-1002_7_flr=on:gsp=input_only:nwc=1.2:nicw=on:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity:updr=off_300",
        "dis+1011_128_bs=off:flr=on:gsp=input_only:lcm=reverse:nwc=1.2:sswsr=on:sgo=on:spo=on:sp=occurrence_900",
        "dis+1_40_bs=off:ecs=on:fsr=off:lcm=predicate:nwc=5:ssec=off:sac=on:sgo=on:spo=on:sp=reverse_arity:updr=off_600",
        "dis+2_2:3_flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=5.0:sio=off:spl=off:updr=off_900",
        "ott-1_50_bs=off:bsr=on:cond=fast:fsr=off:nwc=1.3:ssec=off:sos=on:sio=off:sp=reverse_arity:updr=off_300",
        "lrs+2_14_bs=off:flr=on:gsp=input_only:nwc=3.0:nicw=on:sgo=on:spo=on:sp=reverse_arity_600",
        "dis+4_12_bs=off:gsp=input_only:lcm=predicate:nwc=4:ssec=off:spo=on:sp=occurrence:updr=off_300",
        "dis-2_14_bs=off:cond=fast:flr=on:lcm=predicate:nicw=on:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spl=backtracking:updr=off_600",
        "lrs+10_24_bs=off:cond=fast:flr=on:lcm=reverse:nwc=5:sswn=on:sac=on:sp=reverse_arity_600",
        "dis+1011_128_bs=off:cond=fast:flr=on:gsp=input_only:nwc=2.5:sswsr=on:sgo=on:sp=reverse_arity_300",
        "tab+10_1_gsp=input_only:spl=off:tbsr=off:tfsr=off:tgawr=1/8:tglr=1/7:tipr=off:tlawr=1/8_300",
        "dis+11_50_bs=unit_only:bms=on:gsp=input_only:lcm=reverse:nwc=1.5:nicw=on:sio=off:sp=reverse_arity_300",
        "lrs+1011_24_bs=off:cond=on:flr=on:fsr=off:lcm=reverse:nwc=1.3:ssec=off:sagn=off:sio=off:sp=reverse_arity_300",
        "ott+11_40_bsr=unit_only:cond=fast:flr=on:fsr=off:gsp=input_only:nwc=1.1:ptb=off:ssec=off:spl=backtracking:sp=occurrence_300",
        0
      };
      fallbackSlices = fallback;
    }
    break;

  case Property::FEQ: 
    {
      const char* fallback[] = {
        "lrs+1011_3_bs=unit_only:bsr=unit_only:cond=on:drc=off:gsp=input_only:lcm=reverse:nwc=2.5:ptb=off:ssec=off:sgo=on:sio=off:spl=backtracking:sfv=off_600",
        "dis+1_1_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sswn=on:sd=1:ss=included:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_600",
        "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_600",
        "ott+11_7_bs=off:cond=on:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sio=off:spl=backtracking:sp=occurrence:updr=off_600",
        "lrs-1003_3_bs=unit_only:cond=fast:drc=off:flr=on:fde=none:gs=on:lcm=predicate:nwc=2.5:nicw=on:sp=occurrence_600",
        "ins+1010_4_bs=unit_only:flr=on:gsp=input_only:igbrr=0.9:igrr=1/128:igrp=200:igrpq=1.3:igwr=on:nwc=5:ptb=off:ssec=off:spl=off_300",
        "dis+2_8_drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2:sswn=on:sd=2:sgt=2:ss=axioms:sos=on:sac=on:sgo=on:spo=on:sfv=off:sp=occurrence_300",
        "lrs+10_3:2_bs=off:cond=fast:drc=off:ep=on:fde=none:nwc=10:nicw=on:ptb=off:ssec=off:sd=2:ss=included:sio=off:spl=backtracking_600",
        "dis+2_8:1_bd=off:bsr=unit_only:ep=on:lcm=reverse:nwc=1.1:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=5.0:sos=on:spo=on:sfv=off:sp=reverse_arity_300",
        "ott-1002_28_bd=off:bs=unit_only:bsr=unit_only:ep=on:flr=on:fde=none:lcm=predicate:nwc=5:ptb=off:ssec=off:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_600",
        "dis+1011_8:1_bs=off:bsr=on:cond=fast:fde=none:nwc=1.3:nicw=on:sswn=on:sswsr=on:sd=2:sgt=5:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:updr=off_300",
        "ott+1_2_bs=unit_only:bsr=unit_only:cond=fast:drc=off:lcm=predicate:nwc=3:ptb=off:ssec=off:sd=3:sgt=7:ss=axioms:st=3.0:sos=on:sac=on:spo=on:spl=backtracking:updr=off_300",
        "ins+1010_2:3_bs=off:cond=fast:drc=off:gs=on:igbrr=0.8:igrr=1/4:igrp=200:igrpq=2.0:igwr=on:nwc=10:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_300",
        "lrs+1_8:1_bs=unit_only:bsr=unit_only:drc=off:ep=on:flr=on:gsp=input_only:nwc=4:ptb=off:ssec=off:sd=2:sgt=2:ss=axioms:st=1.2:sos=on:spl=backtracking:sp=occurrence:updr=off_1200",
        "lrs-1010_12_bd=off:bsr=unit_only:cond=fast:drc=off:ep=on:lcm=reverse:nwc=2:nicw=on:ptb=off:ssec=off:sd=4:ss=axioms:sos=on:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_300",
        "dis+1_14_bsr=unit_only:cond=on:drc=off:ep=on:flr=on:fsr=off:fde=none:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sd=10:ss=included:st=1.5:sagn=off:sgo=on:sio=off:spl=backtracking:sfv=off:sp=occurrence:updr=off_1200",
        "dis+1011_14_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:nicw=on:sswn=on:sgo=on:spo=on:sp=reverse_arity_300",
        "ott-4_8:1_bd=off:bs=off:bsr=on:bms=on:cond=fast:drc=off:ep=on:fde=none:gsp=input_only:nwc=1.5:sd=2:sgt=5:ss=axioms:sos=on:sac=on:sgo=on:sio=off:sfv=off_300",
        "lrs+1011_1_bs=unit_only:bsr=unit_only:cond=fast:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.7:sd=1:ss=axioms:st=1.2:sac=on:sgo=on:sp=reverse_arity:updr=off_300",
        "ott+4_7_bs=off:drc=off:fde=none:lcm=predicate:nwc=1.2:nicw=on:ptb=off:ssec=off:sgo=on:spl=backtracking_300",
        "ott+10_3:1_bd=off:bs=off:cond=fast:drc=off:ecs=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.2:ssec=off:sd=3:ss=axioms:sos=on:sio=off:spl=off:sp=occurrence:urr=on_300",
        "dis+1_2:1_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:nwc=4:ptb=off:ssec=off:sswn=on:sswsr=on:sd=2:sgt=15:ss=axioms:sos=on:sac=on:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_300",
        "ott+4_24_bd=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=2:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:st=3.0:sos=on:sac=on:sgo=on:swb=on:sp=occurrence:updr=off_300",
        "lrs-1004_32_fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_600",
        "dis-2_5:4_bd=off:bsr=on:cond=fast:drc=off:ep=on:fsr=off:fde=none:gsp=input_only:gs=on:lcm=reverse:nwc=2:sswsr=on:sos=on:sagn=off:sac=on:spo=on:sp=reverse_arity_300",
        "ott+10_8:1_bs=off:bms=on:br=off:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.3:ssec=off:sos=on:sgo=on:sio=off:urr=on_300",
        "ott+11_14_bd=off:bs=off:bsr=unit_only:drc=off:ep=on:flr=on:fde=none:lcm=predicate:nwc=3:nicw=on:ptb=off:ssec=off:sagn=off:spo=on:spl=backtracking:sp=occurrence:updr=off_300",
        "ott+1011_128_bs=off:bms=on:drc=off:ep=on:flr=on:fsr=off:lcm=predicate:nwc=5:sswn=on:sgo=on:sio=off:sfv=off:sp=reverse_arity_1500",
        "dis-1010_16_bs=off:bsr=unit_only:drc=off:flr=on:fde=none:lcm=reverse:nwc=1.1:nicw=on:ptb=off:ssec=off:sac=on:spl=backtracking:sp=occurrence:updr=off_300",
        "ott+11_5:4_bd=off:bs=unit_only:drc=off:fde=none:lcm=reverse:nwc=1.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_300",
        "dis+1011_64_bd=off:bs=unit_only:bsr=unit_only:drc=off:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=5:ptb=off:ssec=off:sos=on:sagn=off:sgo=on:spl=backtracking:sp=occurrence_300",
        "dis+1004_5:4_bd=off:bs=off:ep=R:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sd=2:sgt=3:ss=axioms:sos=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_300",
        "dis-2_4:1_bs=unit_only:bsr=on:drc=off:lcm=predicate:nwc=1:nicw=on:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:sos=on:sfv=off:sp=occurrence_300",
        "lrs+11_20_bd=off:bs=off:drc=off:flr=on:fsr=off:gsp=input_only:gs=on:nwc=1.1:ptb=off:ssec=off:sd=2:ss=axioms:st=2.0:sgo=on:spo=on:swb=on_900",
        "ott+4_2:3_bs=off:br=off:cond=fast:fsr=off:gsp=input_only:lcm=reverse:nwc=2.5:nicw=on:ptb=off:ssec=off:sos=on:swb=on:sp=occurrence:urr=on:updr=off_300",
        "dis+1002_4:1_bsr=on:bms=on:ep=on:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=3:sswn=on:sd=2:sgt=7:ss=axioms:sos=on:sio=off:sfv=off:sp=reverse_arity_300",
        "dis+1010_40_bd=off:bms=on:cond=fast:drc=off:ecs=on:ep=on:fde=none:gsp=input_only:nwc=2:ssec=off:sgo=on:urr=on_300",
        "dis-1002_128_bsr=unit_only:cond=fast:ep=on:flr=on:nwc=3:sswn=on:sswsr=on:sac=on:sp=occurrence:updr=off_300",
        "lrs+1010_12_bd=off:bs=unit_only:bsr=unit_only:cond=fast:ep=on:flr=on:fde=none:lcm=predicate:nwc=1.1:sswsr=on:sd=4:ss=axioms:st=1.5:sos=on:sagn=off:sgo=on:spo=on:sfv=off:sp=occurrence_300",
        "ott+1_10_bs=unit_only:bsr=unit_only:ep=on:flr=on:nwc=2:ptb=off:ssec=off:sswsr=on:sd=2:sgt=20:ss=axioms:st=1.2:sos=on:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking:sfv=off_300",
        "ott+1010_8:1_bs=off:cond=fast:drc=off:nwc=4:ptb=off:ssec=off:sac=on:spl=backtracking:sfv=off:sp=reverse_arity_300",
        "dis+1010_64_bd=off:bsr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=2:ss=axioms:st=1.5:sos=on:sgo=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity:updr=off_300",
        "dis-1010_5_bd=off:bs=off:cond=fast:ep=on:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_600",
        "dis-2_20_flr=on:fde=none:lcm=predicate:nwc=1.3:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:spl=backtracking_600",
        "lrs+1011_50_bd=off:bs=unit_only:bsr=on:ep=on:fde=none:gsp=input_only:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_900",
        "ott+1_8:1_bs=off:cond=fast:drc=off:ep=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sd=2:sgt=10:ss=axioms:sos=on:sagn=off:sgo=on:spl=backtracking:sfv=off:sp=occurrence_300",
        "dis+11_4:1_bd=off:bs=unit_only:ep=RST:fde=none:gsp=input_only:lcm=reverse:nwc=3:nicw=on:sd=2:sgt=5:ss=axioms:sos=on:sio=off:sfv=off_300",
        "dis+3_4_bs=unit_only:bsr=on:drc=off:ep=RST:fsr=off:nwc=1.3:ssec=off:sd=1:ss=axioms:st=1.2:sos=on:sgo=on:sfv=off_600",
        "ott-1_16_bs=off:cond=fast:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=1.5:ptb=off:ssec=off:sd=1:sgt=3:ss=axioms:st=2.0:swb=on:sfv=off:sp=reverse_arity_300",
        "ott+4_64_bd=off:bs=off:drc=off:gs=on:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:spo=on:spl=backtracking_600",
        "lrs+11_40_bs=off:cond=fast:drc=off:flr=on:fde=none:gsp=input_only:nwc=10:ptb=off:ssec=off:spo=on:spl=backtracking:sp=reverse_arity:updr=off_600",
        "lrs+1_3:2_bs=off:bsr=unit_only:cond=fast:drc=off:fde=none:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sgo=on:spl=backtracking:updr=off_600",
        "ott+1011_3:1_bs=off:ep=on:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sswsr=on:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:updr=off_300",
        "dis-1002_3_bd=off:bs=off:cond=fast:drc=off:ep=R:flr=on:fde=none:nwc=2:nicw=on:ptb=off:ssec=off:sswn=on:ss=included:st=2.0:spl=backtracking:sp=occurrence_300",
        "lrs+1002_24_bsr=on:cond=on:drc=off:flr=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sswn=on:sswsr=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=reverse_arity_300",
        "dis+10_16_bs=off:drc=off:nwc=1.5:nicw=on:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_300",
        "ott-1_20_bd=off:bs=off:drc=off:lcm=predicate:nwc=3:sio=off:spl=off:sp=reverse_arity_300",
        "ott+11_128_fsr=off:fde=none:lcm=reverse:nwc=1:ptb=off:ssec=off:sio=off:spo=on:swb=on:sfv=off:sp=reverse_arity_600",
        "lrs+2_5:1_bd=off:bs=off:bsr=unit_only:cond=fast:drc=off:ecs=on:ep=RST:flr=on:fde=none:gsp=input_only:lcm=reverse:nwc=5:ssec=off:sac=on:sio=off:urr=on_600",
        "ott+3_28_bs=off:bms=on:cond=fast:drc=off:fde=none:gsp=input_only:lcm=predicate:nwc=1.3:nicw=on:ssec=off:sac=on:sgo=on:spo=on_300",
        "ott+11_8:1_bs=off:cond=fast:drc=off:fsr=off:fde=none:nwc=4:sd=3:sgt=7:ss=axioms:sos=on:spo=on:sp=reverse_arity:updr=off_300",
        "ott+1_8_bs=off:drc=off:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sac=on:sgo=on:swb=on:sp=reverse_arity:updr=off_300",
        "dis-1002_2:1_bs=off:drc=off:ep=RS:gs=on:nwc=3:sd=2:ss=axioms:st=5.0:sos=on:sgo=on:sio=off:sp=occurrence_300",
        "dis+11_2_bs=off:bms=on:drc=off:ecs=on:gsp=input_only:gs=on:lcm=predicate:nwc=2:ssec=off:ss=axioms:sos=on:sio=off:spl=off_900",
        "lrs-1010_10_bd=off:bs=unit_only:cond=on:flr=on:gsp=input_only:nwc=1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_600",
        "dis+11_3:2_bs=off:drc=off:ep=R:flr=on:fde=none:nwc=1.7:sos=on:sac=on:sio=off:sp=occurrence_300",
        "dis-2_20_bs=off:drc=off:ep=R:fde=none:lcm=predicate:nwc=1.3:ptb=off:ssec=off:sos=on:sagn=off:sio=off:spo=on:swb=on_300",
        "lrs+10_2_bs=off:br=off:drc=off:gsp=input_only:lcm=predicate:nwc=1.1:nicw=on:ptb=off:ssec=off:sd=1:ss=axioms:st=5.0:sio=off:swb=on:sp=occurrence:urr=on_300",
        "lrs+1011_3:1_bd=off:flr=on:nwc=10:nicw=on:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spo=on:spl=backtracking:sfv=off:sp=occurrence_300",
        "ott+1_2_bs=unit_only:cond=on:drc=off:gsp=input_only:lcm=predicate:nwc=4:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_300",
        "dis+1011_1_bs=off:bsr=unit_only:cond=fast:drc=off:ep=on:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:swb=on:sp=occurrence_300",
        "dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_600",
        "dis+10_4_bs=off:drc=off:fde=none:gsp=input_only:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sac=on:sio=off:swb=on_300",
        "dis+1003_128_bs=off:drc=off:ecs=on:fsr=off:lcm=reverse:nwc=2.5:ssec=off:sos=on:sac=on:sgo=on:spo=on:sp=occurrence_300",
        "lrs-1_2:3_bsr=on:bms=on:ep=RST:fde=none:nwc=10:sd=1:ss=included:sos=on:sio=off:sfv=off:updr=off_600",
        "lrs+2_20_bd=off:bms=on:br=off:cond=on:drc=off:gs=on:lcm=predicate:nwc=1.2:ssec=off:sac=on:sgo=on:urr=on:updr=off_600",
        "dis+1011_1_bd=off:cond=fast:drc=off:ep=on:flr=on:gsp=input_only:lcm=predicate:nwc=2:nicw=on:ptb=off:ssec=off:sgt=7:ss=axioms:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_300",
        "dis-3_128_bs=off:cond=on:drc=off:ep=R:gs=on:nwc=5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_300",
        "lrs+1_3:1_bd=off:bs=off:bsr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:sos=on:sac=on:sio=off:spo=on:spl=backtracking_300",
        "dis-1010_5_bs=off:drc=off:ep=on:gsp=input_only:gs=on:nwc=2.5:ptb=off:ssec=off:sac=on:sgo=on:sio=off:swb=on:sp=reverse_arity_300",
        "ott+1_3_bs=off:bms=on:cond=on:drc=off:ecs=on:fde=none:gsp=input_only:nwc=1.1:ssec=off:sac=on:sgo=on:spo=on_300",
        "dis+11_14_bd=off:bs=off:cond=fast:drc=off:ecs=on:nwc=10:ssec=off:sos=on:sagn=off:sac=on:sgo=on:spo=on:sp=reverse_arity_300",
        "ott-1004_2:3_bd=off:bs=off:cond=fast:drc=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=10:nicw=on:ptb=off:ssec=off:sio=off:spo=on:spl=backtracking:sp=occurrence_300",
        "dis-1004_50_bs=off:drc=off:ep=R:flr=on:fsr=off:nwc=1.3:ssec=off:sos=on:spo=on:updr=off_300",
        "lrs+2_4:1_bs=off:br=off:drc=off:ecs=on:gs=on:lcm=reverse:nwc=2.5:ssec=off:sd=2:ss=axioms:st=5.0:sos=on:sio=off:sp=reverse_arity:urr=on_300",
        "dis+3_20_bd=off:bs=off:drc=off:fsr=off:fde=none:gsp=input_only:gs=on:nwc=1.2:nicw=on:ssec=off:sos=on:sac=on:sgo=on:spo=on_300",
        "dis+11_12_bs=unit_only:cond=on:drc=off:ep=RS:flr=on:fsr=off:gsp=input_only:gs=on:lcm=reverse:nwc=1.5:ptb=off:ssec=off:sos=on:sac=on:spo=on:swb=on:sp=reverse_arity:updr=off_300",
        "dis-10_6_bd=off:bs=off:cond=fast:drc=off:gsp=input_only:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sfv=off:sp=reverse_arity_300",
        "lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_600",
        "ott+1011_40_bd=off:bsr=on:cond=fast:drc=off:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=1.3:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity:updr=off_600",
        "dis+1011_2:3_bs=unit_only:cond=fast:gsp=input_only:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sswn=on:sswsr=on:sd=3:sgt=10:ss=axioms:st=1.2:sos=on:sagn=off:spl=backtracking:updr=off_600",
        "dis+1011_3:2_bd=off:bs=off:bsr=on:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_600",
        "dis+10_3:1_bs=off:br=off:drc=off:fde=none:gs=on:lcm=predicate:nwc=1:nicw=on:ptb=off:ssec=off:sd=3:ss=axioms:st=5.0:sac=on:spo=on:spl=backtracking:sp=reverse_arity:urr=on_900",
        0
      };
      fallbackSlices = fallback;
    }
    break;
  case Property::FNE:
    {
      const char* fallback[] = {
        "dis-1002_3_bs=off:bsr=unit_only:gsp=input_only:gs=on:lcm=reverse:nwc=3:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spo=on:swb=on:sp=occurrence:urr=on:updr=off_300",
        "dis+1011_1_bs=off:cond=fast:gs=on:lcm=predicate:nwc=4:ptb=off:ssec=off:sos=on:sac=on:sgo=on:spo=on:swb=on:sp=reverse_arity_300",
        "dis+4_10_bs=off:ep=on:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_600",
        "dis+1011_128_bsr=on:bms=on:cond=on:fsr=off:lcm=reverse:nwc=4:nicw=on:sswn=on:sswsr=on:sac=on:sio=off:sp=occurrence:updr=off_600",
        "dis+1002_24_bs=off:cond=on:ecs=on:lcm=reverse:ssec=off:spo=on:sp=reverse_arity:updr=off_900",
        "dis+4_128_bs=off:cond=fast:gs=on:lcm=predicate:nwc=5:ptb=off:ssec=off:sos=on:sac=on:sgo=on:sio=off:spo=on:swb=on:sp=occurrence:updr=off_300",
        "dis-10_8:1_bs=off:cond=fast:gsp=input_only:gs=on:nwc=5:ptb=off:ssec=off:sos=on:spl=backtracking:sp=occurrence_900",
        "dis+1004_7_bs=off:lcm=reverse:nwc=1.2:ptb=off:ssec=off:sos=on:sagn=off:spo=on:spl=backtracking:updr=off_900",
        "ott+10_4_bs=off:bms=on:cond=fast:gsp=input_only:gs=on:lcm=reverse:nwc=5:nicw=on:ssec=off:sgo=on:sp=occurrence:urr=on_300",
        "lrs+11_3:2_bs=unit_only:bsr=unit_only:cond=on:fsr=off:lcm=predicate:nwc=1.3:ptb=off:ssec=off:sac=on:spl=backtracking_600",
        "ott+1010_64_bs=off:flr=on:gsp=input_only:lcm=predicate:nwc=5:nicw=on:ptb=off:ssec=off:sagn=off:sgo=on:sio=off:spo=on:spl=backtracking:updr=off_300",
        "dis+2_5:4_bs=off:bms=on:cond=fast:fsr=off:lcm=reverse:nwc=1:ssec=off:sgo=on:sio=off:sp=reverse_arity_300",
        "ott+11_32_bsr=on:cond=on:flr=on:fsr=off:gsp=input_only:lcm=reverse:nwc=5:nicw=on:ptb=off:ssec=off:sos=on:sio=off:spl=backtracking:updr=off_300",
        "dis+10_24_bsr=unit_only:cond=fast:nwc=10:ptb=off:ssec=off:sgo=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity:updr=off_600",
        0
      };
      fallbackSlices = fallback;
    }
    break;
  case Property::EPR:
    {
      const char* fallback[] = {
        "ins+1003_4:1_bs=off:bsr=on:flr=on:fsr=off:fde=none:gsp=input_only:gs=on:igbrr=0.0:igrp=2000:igrpq=2.0:lcm=predicate:nwc=5:ptb=off:ssec=off:sos=on:spl=off:sp=occurrence_300",
        "ott+10_50_bd=off:bs=off:bsr=unit_only:fde=none:gs=on:lcm=predicate:nwc=1:nicw=on:sac=on:sio=off:urr=on_600",
        "dis-1_128_bs=off:bsr=on:bms=on:fde=none:lcm=predicate:nwc=1:ssec=off:sac=on:urr=on_300",
        "ins+3_5:4_bsr=unit_only:cond=on:flr=on:gsp=input_only:igbrr=0.3:igrpq=1.5:nwc=3:ptb=off:ssec=off:spl=off:sp=reverse_arity_2400",
        "ott+1_64_bs=off:cond=on:lcm=predicate:nwc=1.1:sgo=on:spo=on:sp=occurrence:urr=on_300",
        "ins+10_24_bd=off:bs=off:br=off:drc=off:flr=on:fde=none:gsp=input_only:gs=on:igbrr=0.7:igrr=1/4:igrp=700:igrpq=2.0:igwr=on:lcm=reverse:nwc=1.1:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_300",
        "ott+11_50_bd=off:bs=off:cond=on:ecs=on:fde=none:gsp=input_only:lcm=predicate:nwc=4:nicw=on:ssec=off_2100",
        "ins+3_5_bs=off:flr=on:gsp=input_only:igbrr=0.1:igrr=1/32:igrp=700:igrpq=2.0:igwr=on:lcm=predicate:nwc=1:ptb=off:ssec=off:spl=off:sp=reverse_arity:urr=on_300",
        "ins+2_12_bs=off:flr=on:gs=on:igbrr=1.0:igrr=1/64:igrp=400:igrpq=1.0:igwr=on:nwc=2:ptb=off:ssec=off:spl=off:sp=reverse_arity_300",
        "ins-1010_2:3_bs=unit_only:cond=on:flr=on:fsr=off:gsp=input_only:gs=on:igbrr=0.9:igrp=100:igrpq=1.3:lcm=reverse:nwc=1.1:ptb=off:ssec=off:spl=off:sp=reverse_arity:updr=off_2700",
        "ins+4_50_bd=off:bs=off:br=off:cond=fast:drc=off:fsr=off:fde=none:gsp=input_only:gs=on:igbrr=0.6:igrr=1/64:igrp=200:igrpq=1.5:igwr=on:nwc=4:ptb=off:ssec=off:spl=off:sp=occurrence:urr=on_900",
        0
      };
      fallbackSlices = fallback;
    }
    break;
  case Property::UEQ:
    {
      const char* fallback[] = {
	"lrs+10_12_bs=off:bsr=unit_only:drc=off:nwc=1.7_1800",
	"ott+10_20_bs=off:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.1:sp=occurrence_600",
	"ott+10_50_bs=off:drc=off:nwc=10_1200",
	"ott+10_6_bs=off:drc=off:fsr=off:fde=none:nwc=1.2_300",
	"ott+10_8_bd=off:bs=off:drc=off:fsr=off:fde=none:nwc=2:sp=occurrence_300",
	"lrs+10_5:4_bs=off:flr=on:nwc=5.0:sp=occurrence_600",
	"dis+10_128_bs=unit_only:drc=off:fsr=off:fde=none:gsp=input_only:nwc=10_600",
	"lrs+10_2:3_bs=unit_only:bsr=unit_only:drc=off:fde=none:nwc=1.7:sp=occurrence_900",
	"lrs+10_128_bd=off:bs=unit_only:drc=off:gsp=input_only:nwc=1.3:sp=occurrence_600",
	"ott+10_4_bs=off:fde=none:nwc=1.3_1500",
	"ott+10_2:3_bs=off:drc=off:fsr=off:nwc=1.2:sp=occurrence_1500",
	"lrs+10_20_bs=off:drc=off:fsr=off:gsp=input_only:nwc=1.3:sp=occurrence_600",
	"ott+10_4_bs=unit_only:bsr=unit_only:drc=off:nwc=1.7_900",
	"lrs+10_8:1_bs=unit_only:drc=off:gsp=input_only:nwc=2.5:sp=reverse_arity_300",
	"lrs+10_16_bs=unit_only:bsr=unit_only:drc=off:nwc=1.2:sp=occurrence_600",
	"dis+10_5_bs=off:drc=off:fsr=off:gsp=input_only:nwc=5:sp=reverse_arity_600",
	"lrs+10_14_bs=unit_only:drc=off:nwc=1.2:sp=reverse_arity_1800",
	"lrs+10_5:1_bs=off:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.1_600",
	"ott+10_128_bs=off:bsr=unit_only:drc=off:fsr=off:nwc=1.1_1200",
	"dis+10_2:1_bsr=unit_only:drc=off:fsr=off:fde=none:gsp=input_only:nwc=1.5:sp=occurrence_1200",
	"ott+10_2:1_bsr=unit_only:drc=off:fsr=off:fde=none:nwc=4:sp=occurrence_1200",
	"ott+10_5_bd=off:bs=unit_only:drc=off:fsr=off:nwc=4:sp=occurrence_900",
	0
      };
      fallbackSlices = fallback;
    }
    break;
  }
  fallbackSlices = 0;

  int remainingTime=env.remainingTime()/100;
  if(remainingTime<=0) {
    return false;
  }
  StrategySet used;
  if (runSchedule(quickSlices,remainingTime,used)) {
    return true;
  }
  remainingTime=env.remainingTime()/100;
  if(remainingTime<=0) {
    return false;
  }
  return runFallbackSchedule(fallbackSlices,remainingTime,used);
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
 */
bool CASCMode::runSchedule(const char** schedule,unsigned ds,StrategySet& ss)
{
  CALL("CASCMode::runSchedule");

  cout << "Cool!\n"; 
  for (const char** ptr=schedule; *ptr; ptr++) {
    string sliceCode(*ptr);
    cout << sliceCode << "\n";
    string chopped;
    unsigned sliceTime = getSliceTime(sliceCode,chopped);
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
 */
bool CASCMode::runFallbackSchedule(const char** schedule,unsigned ds,StrategySet& ss)
{
  CALL("CASCMode::runFallbackSchedule");

  for (const char** ptr=schedule; *ptr; ptr++) {
    string sliceCode(*ptr);
    string chopped;
    unsigned sliceTime = getSliceTime(sliceCode,chopped);
    if (ss.contains(chopped)) {
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
