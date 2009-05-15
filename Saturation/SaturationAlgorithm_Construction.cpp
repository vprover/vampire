/**
 * @file SaturationAlgorithm_Construction.cpp
 * Implements class SaturationAlgorithm::createFromOptions.
 */

#include "../Lib/Exception.hpp"

#include "../Kernel/KBO.hpp"
#include "../Kernel/LiteralSelector.hpp"

#include "../Shell/Options.hpp"

#include "../Inferences/InferenceEngine.hpp"
#include "../Inferences/BackwardDemodulation.hpp"
#include "../Inferences/BinaryResolution.hpp"
#include "../Inferences/Condensation.hpp"
#include "../Inferences/EqualityFactoring.hpp"
#include "../Inferences/EqualityResolution.hpp"
#include "../Inferences/InterpretedEvaluation.hpp"
#include "../Inferences/Factoring.hpp"
#include "../Inferences/ForwardDemodulation.hpp"
#include "../Inferences/ForwardSubsumptionAndResolution.hpp"
#include "../Inferences/RefutationSeekerFSE.hpp"
#include "../Inferences/SLQueryForwardSubsumption.hpp"
#include "../Inferences/SLQueryBackwardSubsumption.hpp"
#include "../Inferences/Superposition.hpp"
#include "../Inferences/TautologyDeletionISE.hpp"


#include "AWPassiveClauseContainer.hpp"
#include "SaturationAlgorithm.hpp"

#include "Discount.hpp"
#include "LRS.hpp"
#include "Otter.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Inferences;

namespace Construction {

GeneratingInferenceEngineSP createGIE()
{
  CompositeGIE* res=new CompositeGIE();

  res->addFront(GeneratingInferenceEngineSP(new EqualityFactoring()));
  res->addFront(GeneratingInferenceEngineSP(new EqualityResolution()));
  res->addFront(GeneratingInferenceEngineSP(new Superposition()));
  res->addFront(GeneratingInferenceEngineSP(new Factoring()));
  res->addFront(GeneratingInferenceEngineSP(new BinaryResolution()));

  return GeneratingInferenceEngineSP(res);
}

ImmediateSimplificationEngineSP createImmediateSE()
{
  CompositeISE* res=new CompositeISE();

//  res->addFront(ImmediateSimplificationEngineSP(new InterpretedEvaluation()));
  res->addFront(ImmediateSimplificationEngineSP(new TrivialInequalitiesRemovalISE()));
  res->addFront(ImmediateSimplificationEngineSP(new TautologyDeletionISE()));
  res->addFront(ImmediateSimplificationEngineSP(new DuplicateLiteralRemovalISE()));

  return ImmediateSimplificationEngineSP(res);
}

void addFSEs(SaturationAlgorithm* alg)
{
  alg->addForwardSimplifierToFront(ForwardSimplificationEngineSP(new RefutationSeekerFSE()));

  switch(env.options->forwardDemodulation()) {
  case Options::DEMODULATION_ALL:
    alg->addForwardSimplifierToFront(ForwardSimplificationEngineSP(new ForwardDemodulation()));
    break;
  case Options::DEMODULATION_PREORDERED:
    NOT_IMPLEMENTED;
    break;
  case Options::DEMODULATION_OFF:
    break;
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }

  if(env.options->forwardSubsumptionResolution()) {
    if(!env.options->forwardSubsumption()) {
      USER_ERROR("Forward subsumption resolution requires forward subsumption to be enabled.");
    }
    alg->addForwardSimplifierToFront(ForwardSimplificationEngineSP(new ForwardSubsumptionAndResolution()));
  } else if(env.options->forwardSubsumption()) {
    alg->addForwardSimplifierToFront(ForwardSimplificationEngineSP(new SLQueryForwardSubsumption()));
  }

//  alg->addForwardSimplifierToFront(ForwardSimplificationEngineSP(new Condensation()));
}


void addBSEs(SaturationAlgorithm* alg)
{
  switch(env.options->backwardDemodulation()) {
  case Options::DEMODULATION_ALL:
    alg->addBackwardSimplifierToFront(BackwardSimplificationEngineSP(new BackwardDemodulation()));
    break;
  case Options::DEMODULATION_PREORDERED:
    NOT_IMPLEMENTED;
    break;
  case Options::DEMODULATION_OFF:
    break;
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }

  if(env.options->backwardSubsumption()) {
    alg->addBackwardSimplifierToFront(BackwardSimplificationEngineSP(new SLQueryBackwardSubsumption()));
  }
}

LiteralSelectorSP createLiteralSelector()
{
  return LiteralSelectorSP(LiteralSelector::getSelector(env.options->selection()));
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
  case Shell::Options::DISCOUNT:
    res=new Discount(passive, selector);
    break;
  case Shell::Options::LRS:
    res=new LRS(passive, selector);
    break;
  case Shell::Options::OTTER:
    res=new Otter(passive, selector);
    break;
  default:
    NOT_IMPLEMENTED;
  }

  res->setGeneratingInferenceEngine(createGIE());
  res->setImmediateSimplificationEngine(createImmediateSE());
  addFSEs(res);
  addBSEs(res);

  return SaturationAlgorithmSP(res);
}

}
