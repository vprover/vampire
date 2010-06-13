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

#define SLOWNESS 1.35

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
    if(env.timeLimitReached()) {
      env.out()<<"% SZS status Timeout for "<<env.options->problemName()<<endl;
    }
    else {
      env.out()<<"% SZS status GaveUp for "<<env.options->problemName()<<endl;
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

  Property::Category cat = _property.category();
  unsigned prop = _property.props();
  unsigned atoms = _property.atoms();

  cout << "Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!\n";

  const char* backupSlices[] = {
    "dis+10_32_nwc=2.0:sac=on:spl=backtracking_10000",
    "dis+4_8_10000",
    0
  };
  const char* empty[] = {0};
  const char** quickSlices = empty;
  const char** slowSlices = empty; // set to empty for categories having no slow slices

  switch (cat) {
  case Property::NEQ: {
    if (prop & 131072) {
      const char* quick[] = {
	"dis+1010_6_bd=off:nwc=10.0:ssec=off:sac=on:sp=occurrence_1",
	"dis+10_8_bs=off:cond=on:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_49",
	"dis+2_3:1_bd=off:bs=off:ep=on:flr=on:gsp=input_only:lcm=reverse:nwc=3.0:ptb=off:ssec=off:sos=on:sgo=on:spl=backtracking:sp=reverse_arity_14",
	"lrs+1010_1_bs=off:cond=fast:fde=none:gsp=input_only:nwc=1.3:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_77",
	"dis+3_8_bd=off:bs=off:flr=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_137",
	"lrs+10_5_bs=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=3.0:stl=60:sos=on:sio=off:spl=off_24",
	"dis+1002_10_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_43",
	"lrs+4_4_bd=off:cond=on:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=30:sos=on:spl=backtracking:sp=reverse_arity_139",
	"dis+10_8_bd=off:cond=fast:fde=none:nwc=2.0:ssec=off:sgo=on:spo=on:sp=occurrence:updr=off_264",
	"dis+4_10_bd=off:bs=off:cond=fast:fde=none:nwc=10.0:ptb=off:ssec=off:sgo=on:spl=backtracking:sp=reverse_arity_283",
	"lrs-1010_12_bd=off:gsp=input_only:nwc=3.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:sp=reverse_arity:updr=off_46",
	0
      };
      quickSlices = quick;
      const char* slow[] = {
	"dis+10_5_bs=off:cond=on:flr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sp=occurrence_346",
	"lrs+1010_1_bs=off:cond=fast:fde=none:gsp=input_only:nwc=1.3:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_598",
	"dis+3_8_bd=off:bs=off:flr=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_547",
	0
      };
      slowSlices = slow;
      break;
    }
    // prop & 131072 == 0
    const char* quick[] = {
      "lrs-1010_12_bd=off:gsp=input_only:nwc=3.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:sp=reverse_arity:updr=off_8",
      "dis+4_10_bd=off:bs=off:cond=fast:fde=none:nwc=10.0:ptb=off:ssec=off:sgo=on:spl=backtracking:sp=reverse_arity_14",
      "lrs+1010_1_bs=off:cond=fast:fde=none:gsp=input_only:nwc=1.3:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_2",
      "dis+1010_6_bd=off:nwc=10.0:ssec=off:sac=on:sp=occurrence_24",
      "lrs+10_5_bs=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=3.0:stl=60:sos=on:sio=off:spl=off_60",
      "dis+1002_10_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_136",
      "lrs+4_4_bd=off:cond=on:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=30:sos=on:spl=backtracking:sp=reverse_arity_187",
      "dis+10_5_bs=off:cond=on:flr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sp=occurrence_137",
      "dis+3_4_bd=off:bs=off:cond=fast:ep=on:lcm=reverse:nwc=10.0:sswsr=on:sgo=on:sp=occurrence_152",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "dis+10_8_bs=off:cond=on:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_577",
      "lrs+1010_1_bs=off:cond=fast:fde=none:gsp=input_only:nwc=1.3:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_396",
      "lrs-1010_12_bd=off:gsp=input_only:nwc=3.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:sp=reverse_arity:updr=off_394",
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::HEQ: {
    const char* quick[] = {
      "dis+1_4_bd=off:bs=off:cond=on:flr=on:gsp=input_only:lcm=predicate:nwc=5.0:ptb=off:ssec=off:spo=on:spl=backtracking_75",
      "lrs+2_1_bms=on:cond=on:ecs=on:flr=on:gsp=input_only:lcm=predicate:nicw=on:ssec=off:stl=60:sos=on:sac=on:sgo=on:spo=on:sp=reverse_arity_1",
      "dis+2_40_bd=off:bs=off:cond=fast:fsr=off:gsp=input_only:nwc=4.0:ptb=off:ssec=off:sagn=off:sgo=on:sio=off:spl=backtracking:sp=reverse_arity_318",
      "lrs+4_40_cond=on:lcm=predicate:nwc=2:nicw=on:sswn=on:stl=60:sgo=on:sp=occurrence:updr=off_136",
      "lrs+1004_40_bd=off:bms=on:cond=fast:flr=on:nwc=2.0:sswn=on:sswsr=on:stl=60:sio=off:spo=on:sp=occurrence:updr=off_36",
      "lrs-1_5:4_bs=off:cond=fast:ep=on:flr=on:fde=none:nwc=2.0:nicw=on:stl=60:sac=on:sgo=on:sp=reverse_arity:updr=off_76",
      "lrs+1010_5_bd=off:bs=off:bms=on:fde=none:gsp=input_only:nwc=2.5:nicw=on:sswsr=on:stl=60:sgo=on:sio=off:sp=reverse_arity:updr=off_199",
      "lrs-1_40_bd=off:bs=off:cond=fast:fsr=off:lcm=predicate:nwc=10.0:sswn=on:sswsr=on:stl=60:sio=off:spl=off:sp=reverse_arity_65",
      "lrs+10_2_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=10.0:ptb=off:ssec=off:stl=60:sgo=on:sio=off:swb=on:sp=reverse_arity:updr=off_144",
      "lrs+1002_2:3_bs=off:ep=on:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spl=backtracking_151",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "dis+2_40_bd=off:bs=off:cond=fast:fsr=off:gsp=input_only:nwc=4.0:ptb=off:ssec=off:sagn=off:sgo=on:sio=off:spl=backtracking:sp=reverse_arity_399",
      "lrs-1_5:4_bs=off:cond=fast:ep=on:flr=on:fde=none:nwc=2.0:nicw=on:stl=60:sac=on:sgo=on:sp=reverse_arity:updr=off_345",
      "lrs+10_2_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=10.0:ptb=off:ssec=off:stl=60:sgo=on:sio=off:swb=on:sp=reverse_arity:updr=off_229",
      "lrs+1010_5_bd=off:bs=off:bms=on:fde=none:gsp=input_only:nwc=2.5:nicw=on:sswsr=on:stl=60:sgo=on:sio=off:sp=reverse_arity:updr=off_292",
      "dis+2_5_bd=off:bs=off:cond=fast:gsp=input_only:nwc=4.0:nicw=on:sgo=on:sio=off_476",
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::PEQ: {
    const char* quick[] = {
      "lrs+1010_4_cond=on:flr=on:nwc=1.2:nicw=on:sswn=on:stl=90:sac=on:sio=off:spo=on_43",
      "lrs-4_28_bd=off:flr=on:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_1",
      "dis-10_28_ep=on:fsr=off:fde=none:nwc=1.5:ptb=off:ssec=off:sos=on:sgo=on:sp=reverse_arity:updr=off_74",
      "lrs+1003_5_flr=on:fde=none:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:updr=off_132",
      "dis+1003_8_bs=off:flr=on:fsr=off:gsp=input_only:nwc=1.2:ssec=off:sac=on:sgo=on:sio=off:sp=occurrence_113",
      "lrs-1010_8_bs=off:cond=fast:ep=on:fsr=off:gsp=input_only:nwc=1.1:nicw=on:sswn=on:sswsr=on:stl=60:sac=on:updr=off_81",
      "lrs-1_5_bs=off:bms=on:cond=fast:fsr=off:gsp=input_only:nwc=1.2:nicw=on:sswn=on:stl=60:sac=on:sp=reverse_arity_170",
      "lrs+1010_8_cond=on:flr=on:nwc=1:sswn=on:sswsr=on:stl=60:sac=on:sgo=on:spo=on:updr=off_213",
      "dis+10_10_bs=off:ep=on:nwc=1.1:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_311",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "lrs+1010_4_cond=on:flr=on:nwc=1.2:nicw=on:sswn=on:stl=90:sac=on:sio=off:spo=on_482",
      "lrs-4_28_bd=off:flr=on:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=occurrence:updr=off_572",
      "dis-10_28_ep=on:fsr=off:fde=none:nwc=1.5:ptb=off:ssec=off:sos=on:sgo=on:sp=reverse_arity:updr=off_355",
      "dis+10_2_bd=off:cond=on:ecs=on:flr=on:gsp=input_only:nwc=5.0:nicw=on:ssec=off:sio=off:spl=off:sp=occurrence:updr=off_312",
      "dis+1003_8_bs=off:flr=on:fsr=off:gsp=input_only:nwc=1.2:ssec=off:sac=on:sgo=on:sio=off:sp=occurrence_506",
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::HNE: {
    const char* quick[] = {
      "dis+1_40_bs=off:ecs=on:fsr=off:lcm=predicate:nwc=5:ssec=off:sac=on:sgo=on:spo=on:sp=reverse_arity:updr=off_228",
      "lrs+1002_5:4_bs=off:cond=fast:flr=on:fsr=off:gsp=input_only:nicw=on:ptb=off:ssec=off:stl=90:sac=on:sgo=on:sio=off:spl=backtracking_1",
      "lrs+10_3_bs=off:ep=on:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spl=backtracking_270",
      "dis-1004_40_cond=fast:ecs=on:flr=on:fsr=off:gsp=input_only:nicw=on:ssec=off:sac=on:sgo=on:spo=on_153",
      "dis+2_40_cond=fast:flr=on:fsr=off:gsp=input_only:sswn=on:sac=on:sgo=on:spo=on:sp=reverse_arity:updr=off_384",
      "lrs+1002_6_bs=off:cond=fast:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=3.0:ptb=off:ssec=off:stl=60:sio=off:spl=off:sp=reverse_arity:updr=off_145",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "dis+1_40_bs=off:ecs=on:fsr=off:lcm=predicate:nwc=5:ssec=off:sac=on:sgo=on:spo=on:sp=reverse_arity:updr=off_560",
      "lrs+2_14_bs=off:flr=on:gsp=input_only:nwc=3.0:nicw=on:stl=60:sgo=on:spo=on:sp=reverse_arity_524",
      "dis+2_2:1_bs=off:flr=on:nwc=4.0:nicw=on:ssec=off:sac=on:sio=off:sp=reverse_arity:updr=off_796",
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::NNE: {
    const char* quick[] = {
      "dis+2_3_bms=on:gsp=input_only:lcm=reverse:nwc=4.0:sswn=on:sac=on:spo=on_30",
      "dis+10_6_ecs=on:lcm=reverse:nwc=5.0:ssec=off:sio=off:spl=off:sp=reverse_arity:updr=off_48",
      "lrs+1003_28_bs=off:cond=on:lcm=reverse:nwc=3:ptb=off:ssec=off:stl=60:sos=on:sac=on:spl=backtracking:sp=reverse_arity_138",
      "dis-4_8_bs=off:gsp=input_only:nwc=1.7:ptb=off:ssec=off:spl=backtracking:sp=reverse_arity:updr=off_55",
      "lrs+10_10_cond=fast:lcm=reverse:nwc=2.0:sswsr=on:stl=90:sp=reverse_arity:updr=off_132",
      "dis+2_7_bs=off:cond=fast:gsp=input_only:nwc=3.0:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_27",
      "dis+1002_40_bd=off:cond=on:lcm=predicate:nwc=1.7:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_215",
      "lrs+10_5:4_bs=off:ep=on:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spl=backtracking_334",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "dis+4_28_bs=off:gsp=input_only:lcm=reverse:nwc=2.0:ssec=off:sgo=on:spo=on:sp=occurrence_280",
      "lrs+1003_28_bs=off:cond=on:lcm=reverse:nwc=3:ptb=off:ssec=off:stl=60:sos=on:sac=on:spl=backtracking:sp=reverse_arity_309",
      "lrs+10_10_cond=fast:lcm=reverse:nwc=2.0:sswsr=on:stl=90:sp=reverse_arity:updr=off_644",
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::FEQ: {
    if (prop == 0) {
      const char* quick[] = {
	"lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_32",
	"lrs-1003_14_bd=off:bs=off:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=60:ss=included:st=3.0:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_5",
	"dis+1003_16_ep=on:fde=none:nwc=2.5:ssec=off:ss=axioms:st=2.0:sos=on:sac=on:sgo=on:updr=off_7",
	"lrs+4_20_cond=fast:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sac=on:sgo=on:updr=off_22",
	"dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_80",
	"lrs+3_5_bs=off:cond=on:ecs=on:flr=on:nwc=1.1:ssec=off:stl=60:ss=axioms:st=2.0:spo=on:sp=occurrence_141",
	"dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_196",
	"lrs-1004_32_fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spl=backtracking:sp=occurrence_198",
	"dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_96",
	"lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_226",
	"lrs+3_8_bs=off:cond=on:fde=none:gsp=input_only:lcm=predicate:nwc=5.0:nicw=on:ptb=off:ssec=off:stl=30:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_120",
	"lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_7",
	0
      };
      quickSlices = quick;
      const char* slow[] = {
	"lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_307",
	"dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_544",
	"lrs+4_20_cond=fast:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sac=on:sgo=on:updr=off_464",
	"dis+1003_16_ep=on:fde=none:nwc=2.5:ssec=off:ss=axioms:st=2.0:sos=on:sac=on:sgo=on:updr=off_404",
	0
      };
      slowSlices = slow;
      break;
    }
    // prop != 0
    if (prop == 1) {
      const char* quick[] = {
	"lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_5",
	"lrs-1003_14_bd=off:bs=off:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=60:ss=included:st=3.0:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_127",
	"dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_47",
	"dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_124",
	"lrs+4_6_bd=off:bs=off:cond=on:flr=on:fde=none:nwc=4:nicw=on:ptb=off:ssec=off:stl=60:sio=off:spl=backtracking_9",
	"dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_71",
	"lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_58",
	"dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_119",
	"lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_150",
	0
      };
      quickSlices = quick;
      const char* slow[] = {
	"lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_491",
	"lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_410",
	"lrs+4_20_cond=fast:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sac=on:sgo=on:updr=off_440",
	0
      };
      slowSlices = slow;
      break;
    }
    // prop != 0,1
    if (prop == 131087) {
      if (atoms < 1000) {
	const char* quick[] = {
	  "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_31",
	  "dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_14",
	  "dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_1",
	  "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_4",
	  "dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_42",
	  "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_490",
	  "lrs+3_5_bs=off:cond=on:ecs=on:flr=on:nwc=1.1:ssec=off:stl=60:ss=axioms:st=2.0:spo=on:sp=occurrence_104",
	  "lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_250",
	  "dis+1003_16_ep=on:fde=none:nwc=2.5:ssec=off:ss=axioms:st=2.0:sos=on:sac=on:sgo=on:updr=off_253",
	  "dis+10_2:1_bs=off:cond=on:flr=on:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_35",
	  0
	};
	quickSlices = quick;
	break;
      }
      // prop == 131087, atoms >= 1000
      if (atoms < 10000) {
	const char* quick[] = {
	  "lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_37",
	  "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_166",
	  "lrs-1010_4_bd=off:bs=off:cond=fast:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=30:spl=backtracking_69",
	  "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_313",
	  "dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_195",
	  "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_281",
	  0
	};
	quickSlices = quick;
	const char* slow[] = {
	  "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_515",
	  "lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_448",
	  "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_300",
	  0
	};
	slowSlices = slow;
	break;
      }
      // prop == 131087, atoms >= 10000
      if (atoms < 30000) {
	const char* quick[] = {
	  "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_26",
	  "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_63",
	  "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_274",
	  "dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_251",
	  "lrs-1010_4_bd=off:bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:stl=60:ss=axioms:st=2.0:sos=on:spo=on:spl=backtracking:sp=occurrence_344",
	  0
	};
	quickSlices = quick;
	const char* slow[] = {
	  "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_377",
	  "dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_548",
	  "dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_539",
	  "lrs+4_6_bd=off:bs=off:cond=on:flr=on:fde=none:nwc=4:nicw=on:ptb=off:ssec=off:stl=60:sio=off:spl=backtracking_385",
	  0
	};
	slowSlices = slow;
	break;
      }
      // prop == 131087, atoms >= 30000
      if (atoms < 100000) {
	const char* quick[] = {
	  "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_379",
	  "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_144",
	  "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_557",
	  "dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_382",
	  "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_359",
	  0
	};
	quickSlices = quick;
	break;
      }
      // prop == 131087, atoms >= 100000
      const char* quick[] = {
	"lrs-1010_4_bd=off:bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:stl=60:ss=axioms:st=2.0:sos=on:spo=on:spl=backtracking:sp=occurrence_232",
	"dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_529",
	"lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_105",
	"lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_494",
	"dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_541",
	0
      };
      quickSlices = quick;
      break;
    }
    // prop != 0,1,131087
    if (prop == 131073) {
      if (atoms > 500) {
	const char* quick[] = {
	  "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_68",
	  "lrs-1010_4_bd=off:bs=off:cond=fast:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=30:spl=backtracking_273",
	  "dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_4",
	  "dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_178",
	  "dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_32",
	  "lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_102",
	  "dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_329",
	  0
	};
	quickSlices = quick;
	const char* slow[] = {
	  "dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_531",
	  "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_576",
	  "dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_436",
	  0
	};
	slowSlices = slow;
	break;
      }
      // prop == 131073 && atoms <= 500
      if (atoms > 300) {
	const char* quick[] = {
	  "lrs-1010_4_bd=off:bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:stl=60:ss=axioms:st=2.0:sos=on:spo=on:spl=backtracking:sp=occurrence_4",
	  "dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_137",
	  "lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_127",
	  "dis+10_2:1_bs=off:cond=on:flr=on:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_15",
	  "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_159",
	  "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_48",
	  "lrs-1003_14_bd=off:bs=off:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=60:ss=included:st=3.0:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_165",
	  "dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_116",
	  "dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_154",
	  "lrs-1010_4_bd=off:bs=off:cond=fast:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=30:spl=backtracking_95",
	  0
	};
	quickSlices = quick;
	const char* slow[] = {
	  "lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_296",
	  "lrs+3_5_bs=off:cond=on:ecs=on:flr=on:nwc=1.1:ssec=off:stl=60:ss=axioms:st=2.0:spo=on:sp=occurrence_212",
	  "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_254",
	  "dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_534",
	  "lrs-1010_4_bd=off:bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:stl=60:ss=axioms:st=2.0:sos=on:spo=on:spl=backtracking:sp=occurrence_280",
	  0
	};
	slowSlices = slow;
	break;
      }
      // prop == 131073 && atoms <= 300
      const char* quick[] = {
	"lrs-1010_4_bd=off:bs=off:cond=fast:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=30:spl=backtracking_1",
	"lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_5",
	"dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_88",
	"lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_69",
	"dis+1003_16_ep=on:fde=none:nwc=2.5:ssec=off:ss=axioms:st=2.0:sos=on:sac=on:sgo=on:updr=off_3",
	"dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_73",
	"dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_65",
	"dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_173",
	"dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_107",
	"lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_220",
	"dis+10_2:1_bs=off:cond=on:flr=on:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_177",
	"lrs-1010_4_bd=off:bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:stl=60:ss=axioms:st=2.0:sos=on:spo=on:spl=backtracking:sp=occurrence_98",
	"lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_105",
	"dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_63",
	0
      };
      quickSlices = quick;
      const char* slow[] = {
	"dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_187",
	"lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_300",
	"dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_220",
	"lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_478",
	"dis+10_2:1_bs=off:cond=on:flr=on:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_267",
	"dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_559",
	"dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_476",
	"lrs+3_5_bs=off:cond=on:ecs=on:flr=on:nwc=1.1:ssec=off:stl=60:ss=axioms:st=2.0:spo=on:sp=occurrence_513",
	0
      };
      slowSlices = slow;
      break;
    }
    // prop != 0,1,131087,131073
    if ((prop & 131072) == 0) {
      const char* quick[] = {
	"dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_5",
	"dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_10",
	"lrs+4_20_cond=fast:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sac=on:sgo=on:updr=off_40",
	"dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_9",
	"dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_92",
	"dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_351",
	"dis+1004_4_bd=off:bs=off:ep=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=10.0:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_28",
	"lrs+3_5_bs=off:cond=on:ecs=on:flr=on:nwc=1.1:ssec=off:stl=60:ss=axioms:st=2.0:spo=on:sp=occurrence_366",
	"lrs-1004_32_fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spl=backtracking:sp=occurrence_145",
	"lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_204",
	"lrs-1003_14_bd=off:bs=off:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=60:ss=included:st=3.0:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_255",
	0
      };
      quickSlices = quick;
      break;
    }
    // prop != 0,1,131087,131073, prop & 131072 != 0
    if ((prop & 2) == 0) {
      const char* quick[] = {
	"dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_5",
	"lrs+4_20_cond=fast:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sac=on:sgo=on:updr=off_40",
	"dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_9",
	"dis+1004_4_bd=off:bs=off:ep=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=10.0:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_28",
	"dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_10",
	"dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_92",
	"dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_351",
	"lrs+3_5_bs=off:cond=on:ecs=on:flr=on:nwc=1.1:ssec=off:stl=60:ss=axioms:st=2.0:spo=on:sp=occurrence_366",
	"lrs-1004_32_fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sio=off:spl=backtracking:sp=occurrence_145",
	"lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_204",
	"lrs-1003_14_bd=off:bs=off:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=60:ss=included:st=3.0:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_255",
	0
      };
      quickSlices = quick;
      break;
    }
    // prop != 0,1,131087,131073, prop & 131072 != 0, prop & 2 != 0
    if (atoms > 180) {
      const char* quick[] = {
	"lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_96",
	"lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_1",
	"dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_10",
	"dis+1004_4_bd=off:bs=off:ep=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=10.0:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_114",
	"lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_151",
	"dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_271",
	"dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_196",
	"dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_112",
	"dis+1003_16_ep=on:fde=none:nwc=2.5:ssec=off:ss=axioms:st=2.0:sos=on:sac=on:sgo=on:updr=off_449",
	0
      };
      quickSlices = quick;
      break;
    }
    // prop != 0,1,131087,131073, prop & 131072 != 0, prop & 2 != 0, atoms <= 180
    const char* quick[] = {
      "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_1",
      "lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_43",
      "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_22",
      "dis+1004_4_bd=off:bs=off:ep=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=10.0:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_15",
      "dis+10_2:1_bs=off:cond=on:flr=on:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_5",
      "lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_37",
      "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=60:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_185",
      "lrs+4_6_bd=off:bs=off:cond=on:flr=on:fde=none:nwc=4:nicw=on:ptb=off:ssec=off:stl=60:sio=off:spl=backtracking_100",
      "dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_135",
      "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_200",
      "dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_250",
      "dis+1003_16_ep=on:fde=none:nwc=2.5:ssec=off:ss=axioms:st=2.0:sos=on:sac=on:sgo=on:updr=off_149",
      "dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_68",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=30:sac=on:sgo=on:sio=off:spl=backtracking_281",
      "lrs+4_6_bd=off:bs=off:cond=on:flr=on:fde=none:nwc=4:nicw=on:ptb=off:ssec=off:stl=60:sio=off:spl=backtracking_548",
      "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_525",
      "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_344",
      "lrs+3_5_bs=off:cond=on:ecs=on:flr=on:nwc=1.1:ssec=off:stl=60:ss=axioms:st=2.0:spo=on:sp=occurrence_334",
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::FNE: {
    const char* quick[] = {
      "dis+10_10_bs=off:gsp=input_only:lcm=reverse:nwc=10.0:nicw=on:sswn=on:sgo=on_166",
      "dis+4_10_bs=off:ep=on:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_237",
      "dis+2_32_bs=off:flr=on:fsr=off:lcm=reverse:nwc=3:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_143",
      "dis+1004_5_bs=off:flr=on:lcm=predicate:nwc=5.0:ptb=off:ssec=off:sgo=on:swb=on:sp=occurrence_163",
      "dis+1003_8_bms=on:ecs=on:lcm=predicate:nwc=3.0:ssec=off:sgo=on:sio=off:spo=on:sp=occurrence:updr=off_340",
      "dis-4_128_nwc=1.2:ptb=off:ssec=off:sac=on:sgo=on:swb=on:sp=reverse_arity_167",
      0
    };
    quickSlices = quick;
    break;
  }
  case Property::EPR: {
    const char* quick[] = {
      "lrs+1_8_bd=off:cond=fast:ep=RST:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=60:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity:updr=off_414",
      "dis+10_7_bd=off:bs=off:gsp=input_only:nwc=5.0:ptb=off:ssec=off:sac=on:spo=on:spl=backtracking:sp=occurrence:updr=off_596",
      0
    };
    quickSlices = quick;
    break;
  }
  case Property::UEQ: {
    if (prop == 0) {
      const char* quick[] = {
	"lrs+10_14_bs=off:fde=none:stl=60:sp=occurrence_26",
	"lrs+10_5:4_bs=off:nwc=10.0:stl=90:sp=occurrence_362",
	"dis+10_5_bs=off:fsr=off_38",
	"lrs+10_28_nwc=1.1:stl=60_282",
	"lrs+10_5:4_fsr=off:fde=none:nwc=2.5:stl=90:sp=occurrence_239",
	"lrs+10_12_flr=on:nwc=4.0:stl=60:sp=occurrence_493",
	0
      };
      quickSlices = quick;
      break;
    }
    // prop != 0
    if (prop == 2) {
      const char* quick[] = {
	"lrs+10_7_bs=off:nwc=3.0:stl=60:sp=reverse_arity_243",
	"lrs+10_14_bs=off:fde=none:stl=60:sp=occurrence_200",
	"lrs+10_28_nwc=1.1:stl=60_550",
	0
      };
      quickSlices = quick;
      const char* slow[] = {
	"lrs+10_5:4_bs=off:flr=on:nwc=5.0:stl=60:sp=occurrence_558",
	"lrs+10_5:4_fsr=off:fde=none:nwc=2.5:stl=90:sp=occurrence_784",
	"dis+10_5_bs=off:fsr=off_591",
	0
      };
      slowSlices = slow;
      break;
    }
    // prop != 0 && prop != 2
    const char* quick[] = {
      "lrs+10_12_flr=on:nwc=4.0:stl=60:sp=occurrence_155",
      "lrs+10_7_bs=off:nwc=3.0:stl=60:sp=reverse_arity_54",
      "dis+10_3:2_bs=off:fsr=off:nwc=10.0_601",
      "lrs+10_5:4_fsr=off:fde=none:nwc=2.5:stl=90:sp=occurrence_333",
      "lrs+10_28_nwc=1.1:stl=60_558",
      0
    };
    quickSlices = quick;
    break;
  }
  }
  int remainingTime=env.remainingTime()/100;
  if(remainingTime<=0) {
    return false;
  }
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
