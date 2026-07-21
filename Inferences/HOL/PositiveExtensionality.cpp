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
 * @file PositiveExtensionality.cpp
 * Implements class PositiveExtensionality.
 */

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Inference.hpp"

#include "PositiveExtensionality.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct PosExtResultFn
{
  PosExtResultFn(Clause* cl) : _cl(cl) {}

  Clause* operator() (Literal* lit) // f X = g X
  {
    ASS(lit->isEquality());
    ASS(lit->isPositive());

    auto [lhs, rhs] = lit->eqArgs(); // f X and g X
    if (!lhs.isApplication() || !rhs.isApplication()) {
      return nullptr;
    }

    TermList left1 = lhs.lhs();  // f
    TermList right1 = lhs.rhs(); // X

    TermList left2 = rhs.lhs(); // g
    TermList right2 = rhs.rhs(); // X

    if (right1.isTerm() || right2.isTerm() || right1 != right2) {
      return nullptr;
    }

    unsigned var = right1.var(); // X
    // check that X doesn't occur in f and g
    if (isFreeVariableOf(left1, var) || isFreeVariableOf(left2, var)) {
      return nullptr;
    }
    if (_cl->iterLits().any([var,lit](Literal* curr) { return curr != lit && isFreeVariableOf(curr, var); })) {
      return nullptr;
    }

    // f = g
    auto newLit = Literal::createEquality(true, left1, left2, HOL::lhsSort(lhs));

    LiteralStack resLits;
    for (const auto& curr : *_cl) {
      resLits.push(curr == lit ? newLit : curr);
    }

    return Clause::fromStack(resLits, GeneratingInference1(InferenceRule::POSITIVE_EXTENSIONALITY, _cl)); // f = x \/ C'
  }
private:
  Clause* _cl; // f X = g X \/ C'
};

ClauseIterator PositiveExtensionality::generateClauses(Clause* premise)
{
  return pvi(premise->getSelectedLiteralIterator()
    .filter([](Literal* l){ return l->isEquality() && l->isPositive(); })
    .map(PosExtResultFn(premise))
    .filter(NonzeroFn()));
}

}
