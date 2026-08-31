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

#include "Lib/Environment.hpp"
#include "Lib/Random.hpp"

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

  // under randomized simplifications, each subsumption resolution match is with this
  // probability dropped, giving the next match (possibly a proper subsumption, which
  // is never leaky) a chance instead (to be tuned)
  constexpr double RSI_SKIP_PROB = 0.02;
  bool rsi = env.options->randomizedSimplifications();

  static typename ClauseCodeTree<higherOrder>::ClauseMatcher cm;

  cm.init(_ct, cl, _subsumptionResolution);

  Clause* premise;
  int resolvedQueryLit;

  while ((premise = cm.next(resolvedQueryLit))) {
    if (resolvedQueryLit == -1) {
      ASS(satSubs.checkSubsumption(premise, cl));
      premises = pvi(getSingletonIterator(premise));
      env.statistics->forwardSubsumed++;
      cm.reset();
      return true;
    }
    if (rsi && Random::getDouble(0.0,1.0) < RSI_SKIP_PROB) {
      continue; // drop this candidate; the next match gets a chance
    }
    ASS(satSubs.checkSubsumptionResolutionWithLiteral(premise, cl, resolvedQueryLit));

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
