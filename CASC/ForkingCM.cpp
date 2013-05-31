/**
 * @file ForkingCM.cpp
 * Implements class ForkingCM.
 */

#include "Lib/Portability.hpp"

#if !COMPILER_MSVC

#include <cerrno>
#include <ctime>
#include <stdlib.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/wait.h>


#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/ScopedLet.hpp"
#include "Lib/System.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Lib/Sys/Multiprocessing.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Normalisation.hpp"
#include "Shell/Options.hpp"
#include "Shell/Preprocess.hpp"
#include "Saturation/ProvingHelper.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "ForkingCM.hpp"

namespace CASC
{

using namespace Lib;
using namespace Lib::Sys;
using namespace Kernel;
using namespace Saturation;

ForkingCM::ForkingCM()
{
  CALL("ForkingCM::ForkingCM");

  _prb = UIHelper::getInputProblem(*env.options);

  {
    TimeCounter tc(TC_PREPROCESSING);

    //we normalize now so that we don't have to do it in every child Vampire
    ScopedLet<Statistics::ExecutionPhase> phaseLet(env.statistics->phase,Statistics::NORMALIZATION);
    Normalisation norm;
    norm.normalise(*_prb);
  }

  _property = _prb->getProperty();
}

bool ForkingCM::runSlice(Options& opt)
{
  CALL("ForkingCM::runSlice");

  pid_t fres=Multiprocessing::instance()->fork();

  if(!fres) {
    childRun(opt);

    INVALID_OPERATION("ForkingCM::childRun should never return.");
  }

  System::ignoreSIGINT();

  int status;
  errno=0;
  pid_t res=waitpid(fres, &status, 0);
  if(res==-1) {
    SYSTEM_FAIL("Error in waiting for forked process.",errno);
  }

  System::heedSIGINT();

  Timer::syncClock();

  if(res!=fres) {
    INVALID_OPERATION("Invalid waitpid return value: "+Int::toString(res)+"  pid of forked Vampire: "+Int::toString(fres));
  }

  ASS(!WIFSTOPPED(status));

  if( (WIFSIGNALED(status) && WTERMSIG(status)==SIGINT) ||
      (WIFEXITED(status) && WEXITSTATUS(status)==3) )  {
    //if the forked Vampire was terminated by SIGINT (Ctrl+C), we also terminate
    //(3 is the return value for this case; see documentation for the
    //@b vampireReturnValue global variable)

    handleSIGINT();
  }

  if(WIFEXITED(status) && WEXITSTATUS(status)==0) {
    //if Vampire succeeds, its return value is zero
    return true;
  }

  return false;
}

/**
 * Do the theorem proving in a forked-off process
 */
void ForkingCM::childRun(Options& strategyOpt)
{
  CALL("ForkingCM::childRun");

  UIHelper::cascModeChild=true;
  int resultValue=1;
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();

  Options opt(strategyOpt);

  //we have already performed the normalization
  opt.setNormalize(false);
  opt.setForcedOptionValues();
  opt.checkGlobalOptionConstraints();
  *env.options = opt; //just temporarily until we get rid of dependencies on env.options in solving
  env.options->setTimeLimitInDeciseconds(opt.timeLimitInDeciseconds());

  env.beginOutput();
  env.out()<<opt.testId()<<" on "<<env.options->problemName()<<endl;
  env.endOutput();

  ProvingHelper::runVampire(*_prb,opt);

  //set return value to zero if we were successful
#if SATISFIABLE_IS_SUCCESS
  if(env.statistics->terminationReason==Statistics::REFUTATION ||
      env.statistics->terminationReason==Statistics::SATISFIABLE) {
#else
  if(env.statistics->terminationReason==Statistics::REFUTATION) {
#endif
    resultValue=0;
  }

  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

  exit(resultValue);
}

}

#endif // !COMPILER_MSVC
