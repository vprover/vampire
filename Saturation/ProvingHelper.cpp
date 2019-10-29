
/*
 * File ProvingHelper.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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
  catch(ActivationLimitExceededException&) {
    env.statistics->terminationReason=Statistics::ACTIVATION_LIMIT;
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
  catch(ActivationLimitExceededException&) {
    env.statistics->terminationReason=Statistics::ACTIVATION_LIMIT;
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

  Timer::setTimeLimitEnforcement(false); // we catch time limit, but only in the main loop, not the brutal interrupt and System::terminate
  MainLoopResult sres(salg->run());
  if (sres.terminationReason >= Statistics::TerminationReason::REFUTATION_NOT_FOUND) {

    env.beginOutput();
    UIHelper::outputResult(env.out());
    env.endOutput();

    Options* secondStrat = opt.secondStrategy();
    if (secondStrat) {
      salg = nullptr; // clean the smart pointer -> destroy the old salg

      env.options = secondStrat; // because many places in vampire use the global one anyway...

      env.timer->reset();
      env.timer->start();
      salg = MainLoop::createFromOptions(prb, *secondStrat);
      sres = MainLoopResult(salg->run());
    }
  }

  env.statistics->phase=Statistics::FINALIZATION;
  Timer::setTimeLimitEnforcement(false);
  sres.updateStatistics();
}


}
