/*
 * MinimizeInvariants.cpp
 *
 *  Created on: Jun 10, 2013
 *      Author: ioan
 */

#if IS_LINGVA
#include "Lib/Environment.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Timer.hpp"
#include "Lib/TimeCounter.hpp"

#include "Saturation/ProvingHelper.hpp"
#include "Shell/Preprocess.hpp"

#include "MinimizeInvariants.hpp"
#include "Lingva.hpp"

#include "Lib/Int.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include <cerrno>
#include <ctime>
#include <stdlib.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/wait.h>

#include "Lib/Int.hpp"
#include "Lib/ScopedLet.hpp"
#include "Lib/System.hpp"
#include "Lib/Sys/Multiprocessing.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Preprocess.hpp"
#include "Saturation/ProvingHelper.hpp"

#include "Forking.hpp"

using namespace Lib;
using namespace Lib::Sys;
using namespace Program;
using namespace Saturation;
using namespace Program;

void MinimizeInvariants::perform(){
  runSlice(*env.options);
}

void MinimizeInvariants::run(){
  CALL("MinimizeInvariants::perform()");
  //include timer for all the forked processes
  env.timer->makeChildrenIncluded();
  RunLingva lingva;
  Problem* prb = new Problem(lingva.getUnits());
  Forking cm(prb);
  cm.perform();
}


void MinimizeInvariants::handleSIGINT(){
  CALL("MinimizeInvariants::handleSIGINT");
  env.beginOutput();
  env.out()<<"% Terminated by SIGINT!"<<endl;
  env.statistics->print(env.out());
  env.endOutput();
  exit(VAMP_RESULT_STATUS_SIGINT);
}
#endif
