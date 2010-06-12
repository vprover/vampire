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
#include "Lib/System.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Lib/Sys/Multiprocessing.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Normalisation.hpp"
#include "Shell/Options.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "ForkingCM.hpp"

namespace Shell
{
namespace CASC
{

using namespace Lib;
using namespace Lib::Sys;
using namespace Kernel;
using namespace Saturation;

ForkingCM::ForkingCM()
{
  CALL("ForkingCM::ForkingCM");

  _units=UIHelper::getInputUnits();
//  _units=0;
  _property.scan(_units);

  {
    TimeCounter tc(TC_PREPROCESSING);

    //we normalize now so that we don't have to do it in every child Vampire
    env.statistics->phase=Statistics::NORMALIZATION;
    Normalisation norm;
    _units = norm.normalise(_units);
    env.statistics->phase=Statistics::UNKNOWN_PHASE;
  }
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
void ForkingCM::childRun(Options& opt)
{
  CALL("ForkingCM::childRun");

  int resultValue=1;
//  Timer::initTimer();
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();

  *env.options=opt;
  //we have already performed the normalization
  env.options->setNormalize(false);

  env.out<<env.options->testId()<<" on "<<env.options->problemName()<<endl;
  ClauseIterator clauses;
  {
    TimeCounter tc2(TC_PREPROCESSING);

    Preprocess prepro(_property,*env.options);
    //phases for preprocessing are being set inside the proprocess method
    prepro.preprocess(_units);

    clauses=pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(_units)) );
  }
  Unit::onPreprocessingEnd();
  try {
    env.statistics->phase=Statistics::SATURATION;
    SaturationAlgorithmSP salg=SaturationAlgorithm::createFromOptions();
    salg->addInputClauses(clauses);

    SaturationResult sres(salg->saturate());
    env.statistics->phase=Statistics::FINALIZATION;
    Timer::setTimeLimitEnforcement(false);
    sres.updateStatistics();

    //set return value to zero if we were successful
    if(sres.terminationReason==Statistics::REFUTATION) {
      resultValue=0;
    }
  }
  catch(MemoryLimitExceededException) {
    env.statistics->terminationReason=Statistics::MEMORY_LIMIT;
    env.statistics->refutation=0;
    size_t limit=Allocator::getMemoryLimit();
    //add extra 1 MB to allow proper termination
    Allocator::setMemoryLimit(limit+1000000);
  }
  catch(TimeLimitExceededException) {
    env.statistics->terminationReason=Statistics::TIME_LIMIT;
    env.statistics->refutation=0;
  }
  UIHelper::outputResult();

  exit(resultValue);
}

}
}

#endif // !COMPILER_MSVC
