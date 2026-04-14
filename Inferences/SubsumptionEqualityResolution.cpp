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
 * @file SubsumptionEqualityResolution.cpp
 * Implements class SubsumptionEqualityResolution.
 */

#include "Inferences/DemodulationHelper.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SubstHelper.hpp"

#include "SubsumptionEqualityResolution.hpp"

namespace Inferences
{

Clause* SubsumptionEqualityResolution::simplify(Clause* cl)
{
  for (const auto& lit : *cl) {
    if (!lit->isEquality() || lit->isPositive()) {
      continue;
    }

    auto [lhs, rhs] = lit->eqArgs();

    struct Unifier : SubstApplicator {
      bool unify(TermList lhs, TermList rhs) {
        return subst.unify(lhs, 0, rhs, 0);
      }
      TermList operator()(unsigned v) const override {
        return subst.apply(TermList::var(v), 0);
      }
      RobSubstitution subst;
    } unifier;

    if (!unifier.unify(lhs, rhs)) {
      continue;
    }

    RStack<Literal*> resLits;
    for (const auto& curr : *cl) {
      if (lit == curr) {
        continue;
      }
      if (!DemodulationHelper::isRenamingOn(&unifier, curr)) {
        goto fail;
      }
      resLits->push(curr);
    }
    return Clause::fromStack(*resLits, SimplifyingInference1(InferenceRule::SUBSUMPTION_EQUALITY_RESOLUTION, cl));
fail:
    continue;
  }
  return cl;
}

}
