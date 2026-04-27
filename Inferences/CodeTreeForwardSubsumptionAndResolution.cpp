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

#include "Saturation/SaturationAlgorithm.hpp"

#include "ProofExtra.hpp"
#include "CodeTreeForwardSubsumptionAndResolution.hpp"

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

  Clause* premise;
  int resolvedQueryLit;

  while ((premise = cm.next(resolvedQueryLit))) {
    if (resolvedQueryLit == -1) {
      ASS(satSubs.checkSubsumption(premise, cl));
#if DEBUG_CODE_TREES
      if (!satSubs.checkSubsumption(premise, cl)) {
        INVALID_OPERATION(premise->toString()+"sfs "+cl->toString());
      }
#endif

      premises = pvi(getSingletonIterator(premise));
      env.statistics->forwardSubsumed++;
      cm.reset();
      return true;
    }

    ASS(satSubs.checkSubsumptionResolutionWithLiteral(premise, cl, resolvedQueryLit));
#if DEBUG_CODE_TREES
    if(!satSubs.checkSubsumptionResolutionWithLiteral(premise, cl, resolvedQueryLit)) {
      INVALID_OPERATION(premise->toString()+"sfsf "+cl->toString());
    }
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
