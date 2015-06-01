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

#include "InstGen/IGAlgorithm.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Tabulation/TabulationAlgorithm.hpp"

#include "FMB/FiniteModelBuilder.hpp"

#include "Shell/BFNTMainLoop.hpp"
#include "Shell/Options.hpp"

#include "Signature.hpp"
#include "Clause.hpp"
#include "Problem.hpp"

#include "MainLoop.hpp"

using namespace Kernel;
using namespace InstGen;
using namespace Saturation;
using namespace Tabulation;
using namespace FMB;

void MainLoopResult::updateStatistics()
{
  CALL("MainLoopResult::updateStatistics");

  env.statistics->terminationReason = terminationReason;
  env.statistics->refutation = refutation;
  env.statistics->saturatedSet = saturatedSet;
}

/**
 * Run the solving algorithm
 */
MainLoopResult MainLoop::run()
{
  CALL("MainLoop::run");

  try {
    init();
    return runImpl();
  }
  catch(RefutationFoundException& rs)
  {
    return MainLoopResult(Statistics::REFUTATION, rs.refutation);
  }
  catch(TimeLimitExceededException&)
  {
    return MainLoopResult(Statistics::TIME_LIMIT);
  }
  catch(MainLoopFinishedException& e)
  {
    return e.result;
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

  return cl->isEmpty() && cl->noSplits();
}

/**
 * Create local clause simplifier for problem @c prb according to options @c opt
 */
ImmediateSimplificationEngine* MainLoop::createISE(Problem& prb, const Options& opt)
{
  CALL("MainLoop::createImmediateSE");

  CompositeISE* res=new CompositeISE();

  switch(opt.condensation()) {
  case Options::Condensation::ON:
    res->addFront(new Condensation());
    break;
  case Options::Condensation::FAST:
    res->addFront(new FastCondensation());
    break;
  case Options::Condensation::OFF:
    break;
  }

  // Only add if there are distinct groups 
  if(prb.hasEquality() && env.signature->hasDistinctGroups()) {
    res->addFront(new DistinctEqualitySimplifier());
  }
  if(prb.hasInterpretedOperations()) {
    res->addFront(new InterpretedEvaluation());
  }
  if(prb.hasEquality()) {
    res->addFront(new TrivialInequalitiesRemovalISE());
  }
  res->addFront(new TautologyDeletionISE());
  res->addFront(new DuplicateLiteralRemovalISE());

  return res;
}

MainLoop* MainLoop::createFromOptions(Problem& prb, const Options& opt)
{
  CALL("MainLoop::createFromOptions");

  if(opt.bfnt()) {
    return new BFNTMainLoop(prb, opt);
  }

  MainLoop* res;

  switch (opt.saturationAlgorithm()) {
  case Options::SaturationAlgorithm::TABULATION:
    res = new TabulationAlgorithm(prb, opt);
    break;
  case Options::SaturationAlgorithm::INST_GEN:
    res = new IGAlgorithm(prb, opt);
    break;
  case Options::SaturationAlgorithm::FINITE_MODEL_BUILDING:
    res = new FiniteModelBuilder(prb,opt);
    break;
  default:
    res = SaturationAlgorithm::createFromOptions(prb, opt);
    break;
  }

  return res;
}

