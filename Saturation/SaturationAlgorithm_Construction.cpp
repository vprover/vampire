/**
 * @file SaturationAlgorithm_Construction.cpp
 * Implements class SaturationAlgorithm::createFromOptions.
 */

#include "../Lib/Exception.hpp"
#include "SaturationAlgorithm.hpp"

#include "Discount.hpp"
#include "Otter.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;
using namespace Inferences;


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
    res->addFront(ForwardSimplificationEngineSP(new ForwardSubsumptionResolution()));
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
  //TODO: finish
  switch(env.options->selection()) {
  case Shell::Options::OTTER:
    res=new Otter(passiveContainer, literalSelector);
    break;
  case Shell::Options::DISCOUNT:
    res=new Discount(passiveContainer, literalSelector);
    break;
  default:
    NOT_IMPLEMENTED;
  }
}

SaturationAlgorithmSP SaturationAlgorithm::createFromOptions()
{
  PassiveClauseContainerSP passiveContainer=
    PassiveClauseContainerSP(new AWPassiveClauseContainer());
  passiveContainer.pcast<AWPassiveClauseContainer>()->setAgeWeightRatio(1,1);

  CompositeGIE generator;
  BinaryResolution brGIE;
  Factoring fGIE;
  generator.addFront(&fGIE);
  generator.addFront(&brGIE);

  CompositeFSE fwSimplifier;
  fwSimplifier.addFront(&rsFSE);
  fwSimplifier.addFront(&fsrFSE);
//  fwSimplifier.addFront(&slfsFSE);
  fwSimplifier.addFront(&tirFSE);
  fwSimplifier.addFront(&tdFSE);
  fwSimplifier.addFront(&dlrFSE);

  SLQueryBackwardSubsumption slbsBSE;


  //Ordering* ordering=KBO::createReversedAgePreferenceConstantLevels();
  Ordering* ordering=KBO::createArityPreferenceConstantLevels();

  LiteralSelectorSP literalSelector=createLiteralSelector();
//    LiteralSelectorSP(new OrderingLiteralSelector(ordering));
//  HeaviestNegativeLiteralSelector hSelector;


  SaturationAlgorithm* res;
  switch(env.options->saturationAlgorithm()) {
  case Shell::Options::OTTER:
    res=new Otter(passiveContainer, literalSelector);
    break;
  case Shell::Options::DISCOUNT:
    res=new Discount(passiveContainer, literalSelector);
    break;
  default:
    NOT_IMPLEMENTED;
  }

  res->setGeneratingInferenceEngine(createGIE());
  res->setForwardSimplificationEngine(createFSE());
  res->setBackwardSimplificationEngine(createBSE());

  return SaturationAlgorithmSP(res);
}
