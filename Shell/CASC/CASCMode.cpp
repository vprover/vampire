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
    const char* quick[] = {
      "dis+1010_6_bd=off:nwc=10.0:ssec=off:sac=on:sp=occurrence_26",
      "dis+10_8_bs=off:cond=on:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_52",
      "lrs+1010_1_bs=off:cond=fast:fde=none:gsp=input_only:nwc=1.3:ptb=off:ssec=off:stl=63.1:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_81",
      "dis+3_4_bd=off:bs=off:cond=fast:ep=on:lcm=reverse:nwc=10.0:sswsr=on:sgo=on:sp=occurrence_60",
      "dis+4_10_bd=off:bs=off:cond=fast:fde=none:nwc=10.0:ptb=off:ssec=off:sgo=on:spl=backtracking:sp=reverse_arity_145",
      "lrs+10_5_bs=off:flr=on:fde=none:gsp=input_only:lcm=predicate:nwc=3.0:stl=63.1:sos=on:sio=off:spl=off_64",
      "dis+10_5_bs=off:cond=on:flr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sp=occurrence_144",
      "lrs-1010_12_bd=off:gsp=input_only:nwc=3.0:ptb=off:ssec=off:stl=63.1:sos=on:sagn=off:sac=on:spl=backtracking:sp=reverse_arity:updr=off_49",
      "lrs+4_4_bd=off:cond=on:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=31.6:sos=on:spl=backtracking:sp=reverse_arity_146",
      "dis+1002_10_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_143",
      "dis+3_8_bd=off:bs=off:flr=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_144",
      "dis+10_8_bd=off:cond=fast:fde=none:nwc=2.0:ssec=off:sgo=on:spo=on:sp=occurrence:updr=off_145",
      "dis+2_3:1_bd=off:bs=off:ep=on:flr=on:gsp=input_only:lcm=reverse:nwc=3.0:ptb=off:ssec=off:sos=on:sgo=on:spl=backtracking:sp=reverse_arity_15",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "dis+10_8_bd=off:cond=fast:fde=none:nwc=2.0:ssec=off:sgo=on:spo=on:sp=occurrence:updr=off_181",
      "dis+4_10_bd=off:bs=off:cond=fast:fde=none:nwc=10.0:ptb=off:ssec=off:sgo=on:spl=backtracking:sp=reverse_arity_284",
      "lrs+1010_1_bs=off:cond=fast:fde=none:gsp=input_only:nwc=1.3:ptb=off:ssec=off:stl=63.1:sos=on:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_628",
      "lrs+4_4_bd=off:cond=on:ep=on:nwc=1.3:nicw=on:ptb=off:ssec=off:stl=31.6:sos=on:spl=backtracking:sp=reverse_arity_197",
      "dis+3_4_bd=off:bs=off:cond=fast:ep=on:lcm=reverse:nwc=10.0:sswsr=on:sgo=on:sp=occurrence_160",
      "dis+10_5_bs=off:cond=on:flr=on:fde=none:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sp=occurrence_364",
      "dis+10_8_bs=off:cond=on:gsp=input_only:lcm=predicate:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_614",
      "lrs-1010_12_bd=off:gsp=input_only:nwc=3.0:ptb=off:ssec=off:stl=63.1:sos=on:sagn=off:sac=on:spl=backtracking:sp=reverse_arity:updr=off_414",
      "dis+3_8_bd=off:bs=off:flr=on:gsp=input_only:lcm=predicate:nwc=2.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=occurrence_575",
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::HEQ: {
    const char* quick[] = {
      "dis+1_4_bd=off:bs=off:cond=on:flr=on:gsp=input_only:lcm=predicate:nwc=5.0:ptb=off:ssec=off:spo=on:spl=backtracking_79",
      "lrs+2_1_bms=on:cond=on:ecs=on:flr=on:gsp=input_only:lcm=predicate:nicw=on:ssec=off:stl=63.1:sos=on:sac=on:sgo=on:spo=on:sp=reverse_arity_2",
      "dis+2_40_bd=off:bs=off:cond=fast:fsr=off:gsp=input_only:nwc=4.0:ptb=off:ssec=off:sagn=off:sgo=on:sio=off:spl=backtracking:sp=reverse_arity_334",
      "lrs+4_40_cond=on:lcm=predicate:nwc=2:nicw=on:sswn=on:stl=63.1:sgo=on:sp=occurrence:updr=off_143",
      "lrs+1004_40_bd=off:bms=on:cond=fast:flr=on:nwc=2.0:sswn=on:sswsr=on:stl=63.1:sio=off:spo=on:sp=occurrence:updr=off_38",
      "lrs-1_5:4_bs=off:cond=fast:ep=on:flr=on:fde=none:nwc=2.0:nicw=on:stl=63.1:sac=on:sgo=on:sp=reverse_arity:updr=off_80",
      "lrs+1010_5_bd=off:bs=off:bms=on:fde=none:gsp=input_only:nwc=2.5:nicw=on:sswsr=on:stl=63.1:sgo=on:sio=off:sp=reverse_arity:updr=off_209",
      "lrs-1_40_bd=off:bs=off:cond=fast:fsr=off:lcm=predicate:nwc=10.0:sswn=on:sswsr=on:stl=63.1:sio=off:spl=off:sp=reverse_arity_69",
      "lrs+10_2_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=10.0:ptb=off:ssec=off:stl=63.1:sgo=on:sio=off:swb=on:sp=reverse_arity:updr=off_152",
      "lrs+1002_2:3_bs=off:ep=on:nicw=on:ptb=off:ssec=off:stl=63.1:sac=on:sio=off:spl=backtracking_159",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "dis+2_40_bd=off:bs=off:cond=fast:fsr=off:gsp=input_only:nwc=4.0:ptb=off:ssec=off:sagn=off:sgo=on:sio=off:spl=backtracking:sp=reverse_arity_419",
      "lrs-1_5:4_bs=off:cond=fast:ep=on:flr=on:fde=none:nwc=2.0:nicw=on:stl=63.1:sac=on:sgo=on:sp=reverse_arity:updr=off_363",
      "lrs+10_2_bs=off:cond=fast:gsp=input_only:lcm=predicate:nwc=10.0:ptb=off:ssec=off:stl=63.1:sgo=on:sio=off:swb=on:sp=reverse_arity:updr=off_241",
      "lrs+1010_5_bd=off:bs=off:bms=on:fde=none:gsp=input_only:nwc=2.5:nicw=on:sswsr=on:stl=63.1:sgo=on:sio=off:sp=reverse_arity:updr=off_307",
      "dis+2_5_bd=off:bs=off:cond=fast:gsp=input_only:nwc=4.0:nicw=on:sgo=on:sio=off_500",
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::PEQ: {
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
    break;
  }
  case Property::HNE: {
    const char* quick[] = {
      "dis+1_40_bs=off:ecs=on:fsr=off:lcm=predicate:nwc=5:ssec=off:sac=on:sgo=on:spo=on:sp=reverse_arity:updr=off_240",
      "lrs+1002_5:4_bs=off:cond=fast:flr=on:fsr=off:gsp=input_only:nicw=on:ptb=off:ssec=off:stl=94.6:sac=on:sgo=on:sio=off:spl=backtracking_2",
      "lrs+10_3_bs=off:ep=on:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=63.1:sac=on:sio=off:spl=backtracking_284",
      "dis-1004_40_cond=fast:ecs=on:flr=on:fsr=off:gsp=input_only:nicw=on:ssec=off:sac=on:sgo=on:spo=on_161",
      "dis+2_40_cond=fast:flr=on:fsr=off:gsp=input_only:sswn=on:sac=on:sgo=on:spo=on:sp=reverse_arity:updr=off_404",
      "lrs+1002_6_bs=off:cond=fast:flr=on:fsr=off:gsp=input_only:lcm=predicate:nwc=3.0:ptb=off:ssec=off:stl=63.1:sio=off:spl=off:sp=reverse_arity:updr=off_153",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "dis+1_40_bs=off:ecs=on:fsr=off:lcm=predicate:nwc=5:ssec=off:sac=on:sgo=on:spo=on:sp=reverse_arity:updr=off_589",
      "lrs+2_14_bs=off:flr=on:gsp=input_only:nwc=3.0:nicw=on:stl=63.1:sgo=on:spo=on:sp=reverse_arity_551",
      "dis+2_2:1_bs=off:flr=on:nwc=4.0:nicw=on:ssec=off:sac=on:sio=off:sp=reverse_arity:updr=off_836",
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::NNE: {
    const char* quick[] = {
      "dis+2_3_bms=on:gsp=input_only:lcm=reverse:nwc=4.0:sswn=on:sac=on:spo=on_32",
      "dis+10_6_ecs=on:lcm=reverse:nwc=5.0:ssec=off:sio=off:spl=off:sp=reverse_arity:updr=off_51",
      "lrs+1003_28_bs=off:cond=on:lcm=reverse:nwc=3:ptb=off:ssec=off:stl=63.1:sos=on:sac=on:spl=backtracking:sp=reverse_arity_145",
      "dis-4_8_bs=off:gsp=input_only:nwc=1.7:ptb=off:ssec=off:spl=backtracking:sp=reverse_arity:updr=off_58",
      "lrs+10_10_cond=fast:lcm=reverse:nwc=2.0:sswsr=on:stl=94.6:sp=reverse_arity:updr=off_139",
      "dis+2_7_bs=off:cond=fast:gsp=input_only:nwc=3.0:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_29",
      "dis+1002_40_bd=off:cond=on:lcm=predicate:nwc=1.7:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity_226",
      "lrs+10_5:4_bs=off:ep=on:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=63.1:sac=on:sio=off:spl=backtracking_351",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "dis+4_28_bs=off:gsp=input_only:lcm=reverse:nwc=2.0:ssec=off:sgo=on:spo=on:sp=occurrence_295",
      "lrs+1003_28_bs=off:cond=on:lcm=reverse:nwc=3:ptb=off:ssec=off:stl=63.1:sos=on:sac=on:spl=backtracking:sp=reverse_arity_325",
      "lrs+10_10_cond=fast:lcm=reverse:nwc=2.0:sswsr=on:stl=94.6:sp=reverse_arity:updr=off_677",
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::FEQ: {
    const char* quick[] = {
      "dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_104",
      "lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=63.1:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_57",
      "lrs-1010_4_bd=off:bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:stl=63.1:ss=axioms:st=2.0:sos=on:spo=on:spl=backtracking:sp=occurrence_108",
      "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_93",
      "dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_102",
      "dis+10_2:1_bs=off:cond=on:flr=on:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_32",
      "lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=31.6:sac=on:sgo=on:sio=off:spl=backtracking_101",
      "dis+1003_16_ep=on:fde=none:nwc=2.5:ssec=off:ss=axioms:st=2.0:sos=on:sac=on:sgo=on:updr=off_36",
      "lrs-1003_14_bd=off:bs=off:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=63.1:ss=included:st=3.0:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_32",
      "dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_102",
      "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=63.1:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_96",
      "lrs+4_20_cond=fast:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=63.1:sac=on:sgo=on:updr=off_65",
      "lrs+3_5_bs=off:cond=on:ecs=on:flr=on:nwc=1.1:ssec=off:stl=63.1:ss=axioms:st=2.0:spo=on:sp=occurrence_83",
      "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=63.1:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_107",
      "dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_72",
      "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_167",
      "dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_80",
      "dis+1004_4_bd=off:bs=off:ep=on:flr=on:fsr=off:fde=none:gsp=input_only:lcm=predicate:nwc=10.0:ptb=off:ssec=off:sagn=off:sac=on:sio=off:spo=on:spl=backtracking:updr=off_83",
      "lrs-1004_32_fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:stl=63.1:sac=on:sio=off:spl=backtracking:sp=occurrence_70",
      "lrs-1010_4_bd=off:bs=off:cond=fast:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=31.6:spl=backtracking_101",
      "lrs+4_6_bd=off:bs=off:cond=on:flr=on:fde=none:nwc=4:nicw=on:ptb=off:ssec=off:stl=63.1:sio=off:spl=backtracking_106",
      "lrs+3_8_bs=off:cond=on:fde=none:gsp=input_only:lcm=predicate:nwc=5.0:nicw=on:ptb=off:ssec=off:stl=31.6:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_101",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "lrs+1002_5:4_bs=off:flr=on:fde=none:gsp=input_only:nwc=2.0:ptb=off:ssec=off:stl=31.6:sac=on:sgo=on:sio=off:spl=backtracking_311",
      "lrs+3_8_bs=off:cond=on:fde=none:gsp=input_only:lcm=predicate:nwc=5.0:nicw=on:ptb=off:ssec=off:stl=31.6:sagn=off:sac=on:sgo=on:sio=off:spl=backtracking_127",
      "lrs-1010_4_bd=off:bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:stl=63.1:ss=axioms:st=2.0:sos=on:spo=on:spl=backtracking:sp=occurrence_362",
      "dis+2_4_bs=off:ep=on:nwc=1.5:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_500",
      "lrs+1_1_bs=off:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=63.1:sos=on:sagn=off:sac=on:spl=backtracking:updr=off_316",
      "dis+1_6_bd=off:bs=off:lcm=predicate:nwc=1.5:nicw=on:sswsr=on:ss=included:st=1.5:sac=on:sp=occurrence_587",
      "lrs-1003_14_bd=off:bs=off:nwc=1.2:nicw=on:ptb=off:ssec=off:stl=63.1:ss=included:st=3.0:sac=on:sgo=on:sio=off:spl=backtracking:updr=off_268",
      "dis+2_10_bs=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:nwc=2.5:ptb=off:ssec=off:ss=included:sos=on:sgo=on:spl=backtracking:sp=reverse_arity:updr=off_585",
      "lrs-1010_3_bd=off:bs=off:ep=on:fde=none:gsp=input_only:nwc=5.0:ptb=off:ssec=off:stl=63.1:sos=on:sac=on:sgo=on:sio=off:spl=backtracking_519",
      "lrs-1004_32_fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:stl=63.1:sac=on:sio=off:spl=backtracking:sp=occurrence_208",
      "dis+1010_8_bs=off:ep=on:fde=none:lcm=predicate:nwc=1.7:sswn=on:sswsr=on:sac=on:spo=on:sp=occurrence_561",
      "lrs+3_5_bs=off:cond=on:ecs=on:flr=on:nwc=1.1:ssec=off:stl=63.1:ss=axioms:st=2.0:spo=on:sp=occurrence_467",
      "dis-1010_2_bs=off:ep=on:nwc=1.5:sswn=on:sswsr=on:ss=included:st=1.5:sgo=on:sp=occurrence_605",
      "lrs+4_20_cond=fast:lcm=predicate:nwc=5.0:ptb=off:ssec=off:stl=63.1:sac=on:sgo=on:updr=off_488",
      "lrs-1010_4_bd=off:bs=off:cond=fast:lcm=reverse:nwc=2.5:ptb=off:ssec=off:stl=31.6:spl=backtracking_287",
      "lrs+10_8_bs=off:fde=none:lcm=predicate:nwc=1.7:ptb=off:ssec=off:stl=63.1:sac=on:sgo=on:sio=off:spl=backtracking:sp=occurrence_516",
      "dis+1003_16_ep=on:fde=none:nwc=2.5:ssec=off:ss=axioms:st=2.0:sos=on:sac=on:sgo=on:updr=off_472",
      "dis+2_3_bs=off:ep=on:fde=none:nwc=4.0:ptb=off:ssec=off:ss=included:st=1.5:sos=on:sio=off:spl=off:sp=occurrence:updr=off_576",
      "dis-4_5_bd=off:bs=off:ep=RST:fde=none:lcm=predicate:nwc=2.0:nicw=on:ptb=off:ssec=off:ss=included:st=5.0:sio=off:spl=backtracking:updr=off_566",
      "dis+10_2:1_bs=off:cond=on:flr=on:lcm=predicate:nwc=2.5:ptb=off:ssec=off:sos=on:sio=off:spl=off:sp=occurrence_281",
      "lrs+4_6_bd=off:bs=off:cond=on:flr=on:fde=none:nwc=4:nicw=on:ptb=off:ssec=off:stl=63.1:sio=off:spl=backtracking_576",
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::FNE: {
    const char* quick[] = {
      "dis+10_10_bs=off:gsp=input_only:lcm=reverse:nwc=10.0:nicw=on:sswn=on:sgo=on_175",
      "dis+4_10_bs=off:ep=on:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking_249",
      "dis+2_32_bs=off:flr=on:fsr=off:lcm=reverse:nwc=3:nicw=on:ptb=off:ssec=off:sac=on:sio=off:spl=backtracking:sp=reverse_arity_151",
      "dis+1004_5_bs=off:flr=on:lcm=predicate:nwc=5.0:ptb=off:ssec=off:sgo=on:swb=on:sp=occurrence_172",
      "dis+1003_8_bms=on:ecs=on:lcm=predicate:nwc=3.0:ssec=off:sgo=on:sio=off:spo=on:sp=occurrence:updr=off_358",
      "dis-4_128_nwc=1.2:ptb=off:ssec=off:sac=on:sgo=on:swb=on:sp=reverse_arity_176",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::EPR: {
    const char* quick[] = {
      "lrs+1_8_bd=off:cond=fast:ep=RST:nwc=1.1:nicw=on:ptb=off:ssec=off:stl=63.1:sac=on:sgo=on:sio=off:spo=on:spl=backtracking:sp=reverse_arity:updr=off_435",
      "dis+10_7_bd=off:bs=off:gsp=input_only:nwc=5.0:ptb=off:ssec=off:sac=on:spo=on:spl=backtracking:sp=occurrence:updr=off_626",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      0
    };
    slowSlices = slow;
    break;
  }
  case Property::UEQ: {
    const char* quick[] = {
      "lrs+10_7_bs=off:nwc=3.0:stl=63.1:sp=reverse_arity_256",
      "lrs+10_14_bs=off:fde=none:stl=63.1:sp=occurrence_46",
      "dis+10_5_bs=off:fsr=off_40",
      "lrs+10_28_nwc=1.1:stl=63.1_297",
      "lrs+10_5:4_fsr=off:fde=none:nwc=2.5:stl=94.6:sp=occurrence_411",
      "lrs+10_5:4_bs=off:nwc=10.0:stl=94.6:sp=occurrence_381",
      "lrs+10_12_flr=on:nwc=4.0:stl=63.1:sp=occurrence_518",
      0
    };
    quickSlices = quick;
    const char* slow[] = {
      "lrs+10_28_nwc=1.1:stl=63.1_586",
      "lrs+10_5:4_fsr=off:fde=none:nwc=2.5:stl=94.6:sp=occurrence_824",
      "lrs+10_5:4_bs=off:flr=on:nwc=5.0:stl=63.1:sp=occurrence_586",
      "dis+10_5_bs=off:fsr=off_621",
      "dis+10_3:2_bs=off:fsr=off:nwc=10.0_632",
      0
    };
    slowSlices = slow;
    break;
  }
  }
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
