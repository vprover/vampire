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
 * @file CodeTreeBackwardSubsumptionAndResolution.cpp
 * Implements class CodeTreeBackwardSubsumptionAndResolution.
 */

#include "Saturation/SaturationAlgorithm.hpp"
#include "CodeTreeBackwardSubsumptionAndResolution.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"

namespace Inferences {

template<bool higherOrder>
CodeTreeBackwardSubsumptionAndResolution<higherOrder>::CodeTreeBackwardSubsumptionAndResolution(SaturationAlgorithm& salg)
  : _subsumptionResolution(salg.getOptions().forwardSubsumptionResolution()),
    _index(salg.getSimplifyingIndex<BackwardSubsumptionIndex>())
{}

template<bool higherOrder>
void CodeTreeBackwardSubsumptionAndResolution<higherOrder>::perform(Clause* premise, BwSimplificationRecordIterator& simplifications)
{
  ASS(_ct.isEmpty());
  simplifications = BwSimplificationRecordIterator::getEmpty();
  _checked.reset();
  List<BwSimplificationRecord> *simplificationBuffer = List<BwSimplificationRecord>::empty();

  if (premise->length() == 1) {
    auto lit = (*premise)[0];
    for (const auto& qr : iterTraits(_index->getInstances<higherOrder>(lit, false, false))) {
      auto icl = qr.data->clause;
      if (!_checked.insert(icl->number())) {
        continue;
      }
      env.statistics->backwardSubsumed++;
      List<BwSimplificationRecord>::push(BwSimplificationRecord(icl), simplificationBuffer);
    }
    if (_subsumptionResolution) {
      for (const auto& qr : iterTraits(_index->getInstances<higherOrder>(lit, true, false))) {
        auto icl = qr.data->clause;
        if (!_checked.insert(icl->number())) {
          continue;
        }
        auto conclusion = SATSubsumption::SATSubsumptionAndResolution::getSubsumptionResolutionConclusion(icl, qr.data->literal, premise, /*forward=*/false);
        ASS(conclusion)
        List<BwSimplificationRecord>::push(BwSimplificationRecord(icl, conclusion), simplificationBuffer);
      }
    }
    if (simplificationBuffer) {
      simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
    }
    return;
  }

  auto calcFingerprints = [](Clause* cl) {
    unsigned predFP = 0;
    unsigned funFP = 0;
    for (const auto& lit : *cl) {
      predFP = predFP | (1 << lit->functor());
      funFP = funFP | lit->fnFP();
    }
    return std::make_pair(predFP, funFP);
  };

  // We take the least matchable literal, heuristically the heaviest literal currently.
  Literal* lit = (*premise)[0];
  unsigned lmVal = lit->weight();
  for(unsigned i = 1; i < premise->length(); i++) {
    Literal* curr = (*premise)[i];
    unsigned currVal = curr->weight();
    if(currVal > lmVal) {
      lit = curr;
      lmVal = currVal;
    }
  }

  auto [predFP, funFP] = calcFingerprints(premise);

  static typename ClauseCodeTree<higherOrder>::ClauseMatcher cm;

  auto check = [&](Clause* cl) {

    if (!_checked.insert(cl->number())) {
      return;
    }

    if (premise->length() > cl->length() || premise->weight() > cl->weight()) {
      return;
    }

    auto [clPredFP, clFunFP] = calcFingerprints(cl);

    if ((predFP & (~clPredFP)) || (funFP & (~clFunFP))) {
      return;
    }

    if (_ct.isEmpty()) {
      _ct.insert(premise);
    }

    cm.init(&_ct, cl, _subsumptionResolution);
    Clause* temp;
    int resolvedQueryLit;

    if ((temp = cm.next(resolvedQueryLit))) {
      ASS_EQ(temp, premise);
      if (resolvedQueryLit == -1) {
        ASS(satSubs.checkSubsumption(premise, cl));
        env.statistics->backwardSubsumed++;
        List<BwSimplificationRecord>::push(BwSimplificationRecord(cl), simplificationBuffer);
      } else {
        ASS(satSubs.checkSubsumptionResolutionWithLiteral(premise, cl, resolvedQueryLit));

        LiteralStack res;
        for (unsigned i = 0; i < cl->length(); i++) {
          if (i == (unsigned)resolvedQueryLit) {
            continue;
          }
          res.push((*cl)[i]);
        }
        auto conclusion = Clause::fromStack(res, SimplifyingInference2(InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION, cl, premise));
        ASS(conclusion);
        List<BwSimplificationRecord>::push(BwSimplificationRecord(cl, conclusion), simplificationBuffer);
      }
    }
    cm.reset();
  };

  for (const auto& qr : iterTraits(_index->getInstances<higherOrder>(lit, false, false))) {
    check(qr.data->clause);
  }

  for (const auto& qr : iterTraits(_index->getInstances<higherOrder>(lit, true, false))) {
    check(qr.data->clause);
  }

  if (simplificationBuffer) {
    simplifications = pvi(List<BwSimplificationRecord>::Iterator(simplificationBuffer));
  }

  if (!_ct.isEmpty()) {
    _ct.remove(premise);
  }
}

template class CodeTreeBackwardSubsumptionAndResolution<false>;
template class CodeTreeBackwardSubsumptionAndResolution<true>;

} // namespace Inferences
