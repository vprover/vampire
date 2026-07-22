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
 * @file CodeTreeForwardSubsumptionAndResolution.cpp
 * Implements class CodeTreeForwardSubsumptionAndResolution.
 */

#include <iosfwd>

#include "Saturation/SaturationAlgorithm.hpp"

#include "ProofExtra.hpp"
#include "CodeTreeForwardSubsumptionAndResolution.hpp"

namespace Indexing {
std::ostream& codeTreeDebugLog();
}

namespace Inferences {

template<bool higherOrder>
CodeTreeForwardSubsumptionAndResolution<higherOrder>::CodeTreeForwardSubsumptionAndResolution(SaturationAlgorithm& salg)
  : _subsumptionResolution(salg.getOptions().forwardSubsumptionResolution()),
    _index(salg.getSimplifyingIndex<CodeTreeSubsumptionIndex<higherOrder>>()),
    _ct(_index->getClauseCodeTree())
{}

template<bool higherOrder>
bool CodeTreeForwardSubsumptionAndResolution<higherOrder>::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  if (_ct->isEmpty()) {
    return false;
  }

  static typename ClauseCodeTree<higherOrder>::ClauseMatcher cm;

  cm.init(_ct, cl, _subsumptionResolution);
  Indexing::codeTreeDebugLog() << "D = clause({" << cl->toReproducerString() << "});" << std::endl;
  Indexing::codeTreeDebugLog() << "m.init(&wtree, D, "; 
  if (_subsumptionResolution) {
   Indexing::codeTreeDebugLog() << "true);" << std::endl;
  } else {
   Indexing::codeTreeDebugLog() << "false);" << std::endl;
  }
  Indexing::codeTreeDebugLog() << "m.next(resolvedQueryLit);" << std::endl;
  Indexing::codeTreeDebugLog() << "m.reset();" << std::endl; 

  Clause* premise;
  int resolvedQueryLit;

  //std::cout << "Execute on " << cl->toReproducerString() << std::endl;
  while ((premise = cm.next(resolvedQueryLit))) {
    if (resolvedQueryLit == -1) {
      ASS(satSubs.checkSubsumption(premise, cl));
      premises = pvi(getSingletonIterator(premise));
      env.statistics->forwardSubsumed++;
      cm.reset();
      return true;
    }
#if VDEBUG
    bool subsumptionResolutionChecks =
      satSubs.checkSubsumptionResolutionWithLiteral(premise, cl, resolvedQueryLit);
    if(!subsumptionResolutionChecks)  {
      Indexing::codeTreeDebugLog() << "Tree is:" << std::endl;
      Indexing::codeTreeDebugLog() << *_ct <<  std::endl;
      Indexing::codeTreeDebugLog() << "Executed on " << cl->toReproducerString() << std::endl;
      Indexing::codeTreeDebugLog() << "ResolvedQueryLit " << resolvedQueryLit<< std::endl;
      Indexing::codeTreeDebugLog() << "_subsumptionResolution is " << _subsumptionResolution << std::endl;
      if constexpr (higherOrder) {
        Indexing::codeTreeDebugLog() << "higherOrder is true" << std::endl;
      } else {
        Indexing::codeTreeDebugLog() << "higherOrder is false" << std::endl;
      }
    }
    ASS(subsumptionResolutionChecks);
#endif

    LiteralStack res;
    for (unsigned i = 0; i < cl->length(); i++) {
      if (i == (unsigned)resolvedQueryLit) {
        continue;
      }
      res.push((*cl)[i]);
    }
    replacement = Clause::fromStack(res, SimplifyingInference2(InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION, cl, premise));
    if(env.options->proofExtra() == Options::ProofExtra::FULL)
      env.proofExtra.insert(replacement, new LiteralInferenceExtra((*cl)[resolvedQueryLit]));
    premises = pvi(getSingletonIterator(premise));
    cm.reset();
    return true;
  }

  cm.reset();
  return false;
}

template class CodeTreeForwardSubsumptionAndResolution<false>;
template class CodeTreeForwardSubsumptionAndResolution<true>;

} // namespace Inferences
