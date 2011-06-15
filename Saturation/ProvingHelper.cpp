/**
 * @file ProvingHelper.cpp
 * Implements class ProvingHelper.
 */

#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Shell/Preprocess.hpp"
#include "Shell/Property.hpp"

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
void ProvingHelper::runVampireSaturation(ClauseIterator clauses)
{
  CALL("ProvingHelper::runVampireSaturation");

  try {
    runVampireSaturationImpl(clauses);
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
void ProvingHelper::runVampire(UnitList* units, Property* prop)
{
  CALL("ProvingHelper::runVampire");

  try
  {
    ClauseIterator clauses;
    {
      TimeCounter tc2(TC_PREPROCESSING);

      Property prop1;
      if(prop==0) {
	env.statistics->phase=Statistics::PROPERTY_SCANNING;
	prop1.scan(units);

	prop=&prop1;
      }

      Preprocess prepro(*prop,*env.options);
      //phases for preprocessing are being set inside the proprocess method
      prepro.preprocess(units);

      clauses=pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(units)) );
    }
    runVampireSaturationImpl(clauses);
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
}

/**
 * Private version of the @b runVampireSaturation function
 * that is not protected for resource-limit exceptions
 */
void ProvingHelper::runVampireSaturationImpl(ClauseIterator clauses)
{
  CALL("ProvingHelper::runVampireSaturationImpl");

  Unit::onPreprocessingEnd();
  env.statistics->phase=Statistics::SATURATION;
  MainLoopSP salg=MainLoop::createFromOptions();
  salg->addInputClauses(clauses);

  MainLoopResult sres(salg->run());
  env.statistics->phase=Statistics::FINALIZATION;
  Timer::setTimeLimitEnforcement(false);
  sres.updateStatistics();
}


}
