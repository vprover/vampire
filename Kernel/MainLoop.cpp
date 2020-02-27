
/*
 * File MainLoop.cpp.
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
 * @file MainLoop.cpp
 * Implements class MainLoop.
 */


#include "Lib/Environment.hpp"
#include "Lib/SmartPtr.hpp"
#include "Lib/System.hpp"

#include "Inferences/Condensation.hpp"
#include "Inferences/DistinctEqualitySimplifier.hpp"
#include "Inferences/FastCondensation.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Inferences/TermAlgebraReasoning.hpp"
#include "Inferences/TautologyDeletionISE.hpp"
#include "Inferences/EquationalTautologyRemoval.hpp"

#include "InstGen/IGAlgorithm.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "FMB/FiniteModelBuilder.hpp"

#include "SAT/Z3MainLoop.hpp"

#include "Shell/BFNTMainLoop.hpp"
#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"

#include "Signature.hpp"
#include "Clause.hpp"
#include "Problem.hpp"

#include "MainLoop.hpp"

using namespace Kernel;
using namespace InstGen;
using namespace Saturation;
using namespace FMB;

void MainLoopResult::updateStatistics()
{
  CALL("MainLoopResult::updateStatistics");

  env.statistics->terminationReason = terminationReason;
  env.statistics->refutation = refutation;
  env.statistics->saturatedSet = saturatedSet;
  if(refutation) {
    env.statistics->maxInductionDepth = refutation->inference()->inductionDepth();
  }
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
  catch(ActivationLimitExceededException&)
  {
    return MainLoopResult(Statistics::ACTIVATION_LIMIT);
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

  if(prb.hasEquality() && opt.equationalTautologyRemoval()) {
    res->addFront(new EquationalTautologyRemoval());
  }

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
  if(prb.hasEquality() && env.signature->hasTermAlgebras()) {
    if (opt.termAlgebraInferences()) {
      res->addFront(new DistinctnessISE());
      res->addFront(new InjectivityISE());
      res->addFront(new NegativeInjectivityISE());
    }
  }
  if(prb.hasInterpretedOperations() || prb.hasInterpretedEquality()) {
    res->addFront(new InterpretedEvaluation());
  }
  if(prb.hasEquality()) {
    res->addFront(new TrivialInequalitiesRemovalISE());
  }
  res->addFront(new TautologyDeletionISE());
  res->addFront(new DuplicateLiteralRemovalISE());

  if(prb.hasEquality() && env.signature->getNat() != nullptr) {
    res->addFront(new TwoSuccessorsISE());
  }
  return res;
}

MainLoop* MainLoop::createFromOptions(Problem& prb, const Options& opt)
{
  CALL("MainLoop::createFromOptions");

  if(opt.bfnt()) {
    return new BFNTMainLoop(prb, opt);
  }

#if VZ3
  bool isComplete = false; // artificially prevent smtForGround from running

  if(isComplete && opt.smtForGround() && prb.getProperty()->allNonTheoryClausesGround() 
                        && prb.getProperty()->hasInterpretedOperations()){
    return new SAT::Z3MainLoop(prb,opt);
  }
#endif

  MainLoop* res;

  switch (opt.saturationAlgorithm()) {
  case Options::SaturationAlgorithm::INST_GEN:
    res = new IGAlgorithm(prb, opt);
    break;
  case Options::SaturationAlgorithm::FINITE_MODEL_BUILDING:
    res = new FiniteModelBuilder(prb,opt);
    break;
#if VZ3
  case Options::SaturationAlgorithm::Z3:
    if(!isComplete || !prb.getProperty()->allNonTheoryClausesGround()){
      reportSpiderStatus('u');
      USER_ERROR("Z3 saturation algorithm is only appropriate where preprocessing produces a ground problem"); 
      //TODO should return inappropriate result instead of error
    }
    res = new SAT::Z3MainLoop(prb,opt);
    break;
#endif
  default:
    res = SaturationAlgorithm::createFromOptions(prb, opt);
    break;
  }

  return res;
}

