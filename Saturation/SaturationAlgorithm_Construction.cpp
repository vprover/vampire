/**
 * @file SaturationAlgorithm_Construction.cpp
 * Implements class SaturationAlgorithm::createFromOptions.
 */

#include "../Lib/Exception.hpp"

#include "../Kernel/KBO.hpp"
#include "../Kernel/OrderingLiteralSelector.hpp"

#include "../Shell/Options.hpp"

#include "../Inferences/InferenceEngine.hpp"
#include "../Inferences/BinaryResolution.hpp"
#include "../Inferences/Factoring.hpp"
#include "../Inferences/ForwardSubsumptionAndResolution.hpp"
#include "../Inferences/RefutationSeekerFSE.hpp"
#include "../Inferences/SLQueryForwardSubsumption.hpp"
#include "../Inferences/SLQueryBackwardSubsumption.hpp"
#include "../Inferences/TautologyDeletionFSE.hpp"


#include "AWPassiveClauseContainer.hpp"
#include "SaturationAlgorithm.hpp"

#include "Discount.hpp"
#include "Otter.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;
using namespace Inferences;

namespace Construction {

GeneratingInferenceEngineSP createGIE()
{
  CompositeGIE* res=new CompositeGIE();

  res->addFront(GeneratingInferenceEngineSP(new Factoring()));
  res->addFront(GeneratingInferenceEngineSP(new BinaryResolution()));

  return GeneratingInferenceEngineSP(res);
}

ForwardSimplificationEngineSP createFSE()
{
  CompositeFSE* res=new CompositeFSE();

  res->addFront(ForwardSimplificationEngineSP(new RefutationSeekerFSE()));

  if(env.options->forwardSubsumptionResolution()) {
    if(!env.options->forwardSubsumption()) {
      USER_ERROR("Forward subsumption resolution requires forward subsumption to be enabled.");
    }
    res->addFront(ForwardSimplificationEngineSP(new ForwardSubsumptionAndResolution()));
  } else if(env.options->forwardSubsumption()) {
    res->addFront(ForwardSimplificationEngineSP(new SLQueryForwardSubsumption()));
  }

  res->addFront(ForwardSimplificationEngineSP(new TrivialInequalitiesRemovalFSE()));
  res->addFront(ForwardSimplificationEngineSP(new TautologyDeletionFSE()));
  res->addFront(ForwardSimplificationEngineSP(new DuplicateLiteralRemovalFSE()));

  return ForwardSimplificationEngineSP(res);
}


BackwardSimplificationEngineSP createBSE()
{
  if(env.options->backwardSubsumption()) {
    return BackwardSimplificationEngineSP(new SLQueryBackwardSubsumption());
  } else {
    return BackwardSimplificationEngineSP(new DummyBSE());
  }
}

LiteralSelectorSP createLiteralSelector()
{
  LiteralSelector* res;
  switch(env.options->literalComparisonMode()) {
  case Shell::Options::LCM_STANDARD:
    res=new OrderingLiteralSelector();
    break;
  default:
    NOT_IMPLEMENTED;
  }
  return LiteralSelectorSP(res);
}

PassiveClauseContainerSP createPassiveContainer()
{
  AWPassiveClauseContainer* res=new AWPassiveClauseContainer();
  res->setAgeWeightRatio(env.options->ageRatio(),env.options->weightRatio());
  return PassiveClauseContainerSP(res);
}

};

using namespace Construction;

SaturationAlgorithmSP SaturationAlgorithm::createFromOptions()
{
  PassiveClauseContainerSP passive=createPassiveContainer();
  LiteralSelectorSP selector=createLiteralSelector();

  SaturationAlgorithm* res;
  switch(env.options->saturationAlgorithm()) {
  case Shell::Options::OTTER:
    res=new Otter(passive, selector);
    break;
  case Shell::Options::DISCOUNT:
    res=new Discount(passive, selector);
    break;
  default:
    NOT_IMPLEMENTED;
  }

  res->setGeneratingInferenceEngine(createGIE());
  res->setForwardSimplificationEngine(createFSE());
  res->setBackwardSimplificationEngine(createBSE());

  return SaturationAlgorithmSP(res);
}
