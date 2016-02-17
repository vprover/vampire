/**
 * @file ProvingHelper.cpp
 * Implements class ProvingHelper.
 */

#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Kernel/Problem.hpp"

#include "Shell/Options.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Property.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/Infinox.hpp"

#include "LabelFinder.hpp"
#include "SaturationAlgorithm.hpp"

#include "ProvingHelper.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;

/**
 * Run the Vampire saturation loop (based on the content of @b env.options )
 * on @b clauses
 *
 * The result of the loop is in @b env.statistics
 *
 * The content of the @b units list after return from the function is
 * undefined
 *
 * The function does not necessarily return (e.g. in the case of timeout,
 * the process is aborted)
 */
  void ProvingHelper::runVampireSaturation(Problem& prb, const Options& opt)
{
  CALL("ProvingHelper::runVampireSaturation");

  try {
    runVampireSaturationImpl(prb, opt);
  }
  catch(MemoryLimitExceededException&) {
    env.statistics->terminationReason=Statistics::MEMORY_LIMIT;
    env.statistics->refutation=0;
    size_t limit=Allocator::getMemoryLimit();
    //add extra 1 MB to allow proper termination
    Allocator::setMemoryLimit(limit+1000000);
  }
  catch(TimeLimitExceededException&) {
    env.statistics->terminationReason=Statistics::TIME_LIMIT;
    env.statistics->refutation=0;
  }
}

/**
 * Run the Vampire preprocessing and saturation loop (based on the content
 * of @b env.options ) on @b units. If @b prop is nonzero, do not scan
 * properties of the units, but use @b prop as a property object instead.
 *
 * The result of the loop is in @b env.statistics
 *
 * The content of the @b units list after return from the function is
 * undefined
 *
 * The function does not necessarily return (e.g. in the case of timeout,
 * the process is aborted)
 */
void ProvingHelper::runVampire(Problem& prb, const Options& opt)
{
  CALL("ProvingHelper::runVampire");

  try
  {
    ClauseIterator clauses;
    {
      TimeCounter tc2(TC_PREPROCESSING);

      Preprocess prepro(opt);
      prepro.preprocess(prb);
    }
    runVampireSaturationImpl(prb, opt);
  }
  catch(MemoryLimitExceededException&) {
    env.statistics->terminationReason=Statistics::MEMORY_LIMIT;
    env.statistics->refutation=0;
    size_t limit=Allocator::getMemoryLimit();
    //add extra 1 MB to allow proper termination
    Allocator::setMemoryLimit(limit+1000000);
  }
  catch(TimeLimitExceededException&) {
    env.statistics->terminationReason=Statistics::TIME_LIMIT;
    env.statistics->refutation=0;
  }
}

/**
 * Private version of the @b runVampireSaturation function
 * that is not protected for resource-limit exceptions
 */
  void ProvingHelper::runVampireSaturationImpl(Problem& prb, const Options& opt)
{
  CALL("ProvingHelper::runVampireSaturationImpl");

  Unit::onPreprocessingEnd();
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] onPreprocessingEnd(), Proving Helper" << std::endl;
    UIHelper::outputAllPremises(env.out(), prb.units(), "New: ");
    env.endOutput();
  }

  env.statistics->phase=Statistics::SATURATION;
  ScopedPtr<MainLoop> salg(MainLoop::createFromOptions(prb, opt));

  LabelFinder* labelFinder = 0;
  if(env.options->mode()==Options::Mode::INFINOX){
    labelFinder = new LabelFinder();
    salg->setLabelFinder(labelFinder);
  }
  
  try{
    MainLoopResult sres(salg->run());
    env.statistics->phase=Statistics::FINALIZATION;
    Timer::setTimeLimitEnforcement(false);
    sres.updateStatistics();
  }catch(TimeLimitExceededException& e){
    if(labelFinder){
      Infinox::checkLabels(labelFinder);
    }
    throw e;
  }
  if(labelFinder){
    Infinox::checkLabels(labelFinder);
  } 

}


}
