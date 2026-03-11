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
 * @file BetaEtaSimplify.cpp
 * Implements class BetaEtaSimplify.
 */

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "BetaEtaSimplify.hpp"

using namespace Lib;
using namespace Kernel;

namespace Inferences {

Clause* BetaEtaSimplify::simplify(Clause* c)
{
  LiteralStack litStack;
  bool modified = false;

  for (const auto& lit : *c) {
    ASS(lit->isEquality());
    auto lhs = lit->termArg(0);
    auto rhs = lit->termArg(1);

    TermList lhsr = HOL::reduce::betaEtaNF(lhs);
    TermList rhsr = HOL::reduce::betaEtaNF(rhs);

    if (lhs != lhsr || rhs != rhsr) {
      modified = true;
      litStack.push(Literal::createEquality(lit->polarity(), lhsr, rhsr, SortHelper::getEqualityArgumentSort(lit)));
      continue;
    }
    litStack.push(lit);
  }

  if (!modified) {
    return c;
  }
  return Clause::fromStack(litStack, SimplifyingInference1(InferenceRule::BETA_ETA_NORMALIZATION, c));
}

}