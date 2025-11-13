/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file ProvingHelper.cpp
 * Implements class ProvingHelper.
 */

#include "Lib/Environment.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/Timer.hpp"

#include "Kernel/Problem.hpp"

#include "Shell/Options.hpp"
#include "Shell/Preprocess.hpp"
#include "Kernel/MainLoop.hpp"
#include "Shell/UIHelper.hpp"

#include "Indexing/TermSharing.hpp"

#include "ProvingHelper.hpp"

namespace Saturation
{

using namespace std;
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
  try {
    runVampireSaturationImpl(prb, opt);
  }
  catch(const std::bad_alloc &) {
    env.statistics->terminationReason=TerminationReason::MEMORY_LIMIT;
    env.statistics->refutation=0;
  }
  catch(TimeLimitExceededException&) {
    env.statistics->terminationReason=TerminationReason::TIME_LIMIT;
    env.statistics->refutation=0;
  }
  catch(ActivationLimitExceededException&) {
    env.statistics->terminationReason=TerminationReason::ACTIVATION_LIMIT;
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
  // Here officially starts preprocessing of the porfolio mode (separately for each worker)
  // and that's the moment we want to set the random seed
  // (no randomness in parsing, for the peace of mind - parsing was done by the master process!)
  // the main reason being that we want to stay in sync with what vampire mode does
  // cf getPreprocessedProblem in vampire.cpp
  if (opt.randomSeed() != 0) {
    Lib::Random::setSeed(opt.randomSeed());
  } else {
    Lib::Random::resetSeed();
  }

  try
  {
    ClauseIterator clauses;
    {
      TIME_TRACE(TimeTrace::PREPROCESSING);

      Preprocess prepro(opt);
      prepro.preprocess(prb);
    }
    runVampireSaturationImpl(prb, opt);
  }
  catch(const std::bad_alloc &) {
    env.statistics->terminationReason=TerminationReason::MEMORY_LIMIT;
    env.statistics->refutation=0;
  }
  catch(TimeLimitExceededException&) {
    env.statistics->terminationReason=TerminationReason::TIME_LIMIT;
    env.statistics->refutation=0;
  }
  catch(ActivationLimitExceededException&) {
    env.statistics->terminationReason=TerminationReason::ACTIVATION_LIMIT;
    env.statistics->refutation=0;
  }
}

/**
 * Private version of the @b runVampireSaturation function
 * that is not protected for resource-limit exceptions
 */
  void ProvingHelper::runVampireSaturationImpl(Problem& prb, const Options& opt)
{
  Unit::onPreprocessingEnd();
  if (env.options->showPreprocessing()) {
    std::cout << "[PP] onPreprocessingEnd(), Proving Helper" << std::endl;
    UIHelper::outputAllPremises(std::cout, prb.units(), "New: ");
  }

  //decide whether to use poly or mono well-typedness test
  //after options have been read. Equality Proxy can introduce poly in mono.
  env.sharing->setPoly();

  env.options->resolveAwayAutoValues(prb);

  env.statistics->phase=ExecutionPhase::SATURATION;
  ScopedPtr<MainLoop> salg(MainLoop::createFromOptions(prb, opt));

  MainLoopResult sres(salg->run());
  env.statistics->phase=ExecutionPhase::FINALIZATION;
  Timer::disableLimitEnforcement();
  sres.updateStatistics();
}


}
