/**
 * @file MainLoop.cpp
 * Implements class MainLoop.
 */


#include "Lib/Environment.hpp"
#include "Lib/SmartPtr.hpp"

#include "Inferences/Condensation.hpp"
#include "Inferences/DistinctEqualitySimplifier.hpp"
#include "Inferences/FastCondensation.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Inferences/TautologyDeletionISE.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "BDD.hpp"
#include "Clause.hpp"

#include "MainLoop.hpp"

namespace Kernel
{

using namespace Saturation;

void MainLoopResult::updateStatistics()
{
  env.statistics->terminationReason=terminationReason;
  env.statistics->refutation=refutation;
}


///////////////////////
// MainLoop
//

MainLoopResult MainLoop::run()
{
  CALL("MainLoop::run");

  try {
    return runImpl();
  }
  catch(RefutationFoundException rs)
  {
    return MainLoopResult(Statistics::REFUTATION, rs.refutation);
  }
  catch(TimeLimitExceededException)
  {
    return MainLoopResult(Statistics::TIME_LIMIT);
  }
}

/**
 * Return true iff clause @b c is refutation clause.
 *
 * Deriving a refutation clause means that the saturation algorithm can
 * terminate with success.
 */
bool MainLoop::isRefutation(Clause* cl)
{
  CALL("MainLoop::isRefutation");

  BDD* bdd=BDD::instance();
  return cl->isEmpty() && (!cl->prop() || bdd->isFalse(cl->prop())) && cl->noSplits();
}

ImmediateSimplificationEngineSP MainLoop::createISE()
{
  CALL("MainLoop::createImmediateSE");

  CompositeISE* res=new CompositeISE();

  switch(env.options->condensation()) {
  case Options::CONDENSATION_ON:
    res->addFront(ImmediateSimplificationEngineSP(new Condensation()));
    break;
  case Options::CONDENSATION_FAST:
    res->addFront(ImmediateSimplificationEngineSP(new FastCondensation()));
    break;
  case Options::CONDENSATION_OFF:
    break;
  }

  res->addFront(ImmediateSimplificationEngineSP(new DistinctEqualitySimplifier()));
  if(env.options->interpretedEvaluation()) {
    res->addFront(ImmediateSimplificationEngineSP(new InterpretedEvaluation()));
  }
  res->addFront(ImmediateSimplificationEngineSP(new TrivialInequalitiesRemovalISE()));
  res->addFront(ImmediateSimplificationEngineSP(new TautologyDeletionISE()));
  res->addFront(ImmediateSimplificationEngineSP(new DuplicateLiteralRemovalISE()));

  return ImmediateSimplificationEngineSP(res);
}


MainLoopSP MainLoop::createFromOptions()
{
  return SaturationAlgorithm::createFromOptions().spcast<MainLoop>();
}

}
