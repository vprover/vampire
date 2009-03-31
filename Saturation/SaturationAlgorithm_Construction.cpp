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
#include "../Inferences/TautologyDeletionFSE.hpp"


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

ForwardSimplificationEngineSP createFSE()
{
  CompositeFSE* res=new CompositeFSE();

  res->addFront(ForwardSimplificationEngineSP(new RefutationSeekerFSE()));

  switch(env.options->forwardDemodulation()) {
  case Options::DEMODULATION_ALL:
    res->addFront(ForwardSimplificationEngineSP(new ForwardDemodulation()));
    break;
  case Options::DEMODULATION_PREORDERED:
    NOT_IMPLEMENTED;
    break;
#if VDEBUG
  case Options::DEMODULATION_OFF:
    break;
  default:
    ASSERTION_VIOLATION;
#endif
  }

  if(env.options->forwardSubsumptionResolution()) {
    if(!env.options->forwardSubsumption()) {
      USER_ERROR("Forward subsumption resolution requires forward subsumption to be enabled.");
    }
    res->addFront(ForwardSimplificationEngineSP(new ForwardSubsumptionAndResolution()));
  } else if(env.options->forwardSubsumption()) {
    res->addFront(ForwardSimplificationEngineSP(new SLQueryForwardSubsumption()));
  }

//  res->addFront(ForwardSimplificationEngineSP(new Condensation()));
  res->addFront(ForwardSimplificationEngineSP(new TrivialInequalitiesRemovalFSE()));
  res->addFront(ForwardSimplificationEngineSP(new TautologyDeletionFSE()));
  res->addFront(ForwardSimplificationEngineSP(new InterpretedEvaluation()));
  res->addFront(ForwardSimplificationEngineSP(new DuplicateLiteralRemovalFSE()));

  return ForwardSimplificationEngineSP(res);
}


BackwardSimplificationEngineSP createBSE()
{
  CompositeBSE* res=new CompositeBSE();

  switch(env.options->backwardDemodulation()) {
  case Options::DEMODULATION_ALL:
    res->addFront(BackwardSimplificationEngineSP(new BackwardDemodulation()));
    break;
  case Options::DEMODULATION_PREORDERED:
    NOT_IMPLEMENTED;
    break;
#if VDEBUG
  case Options::DEMODULATION_OFF:
    break;
  default:
    ASSERTION_VIOLATION;
#endif
  }

  if(env.options->backwardSubsumption()) {
    res->addFront(BackwardSimplificationEngineSP(new SLQueryBackwardSubsumption()));
  }

  return BackwardSimplificationEngineSP(res);
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
  res->setForwardSimplificationEngine(createFSE());
  res->setBackwardSimplificationEngine(createBSE());

  return SaturationAlgorithmSP(res);
}

}
