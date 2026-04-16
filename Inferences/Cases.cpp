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
 * @file Cases.cpp
 * Higher-order variant of FOOL paramodulation.
 * @see FOOLParamodulation class.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Cases.hpp"

namespace Inferences {

using namespace std;

Cases::Cases(SaturationAlgorithm& salg) : _ord(salg.getOrdering()) {}

Clause* performCases(Clause* premise, Literal* lit, TermList t)
{
  ASS(t.isTerm());

  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());

  // Found a boolean term! Create the C[true] \/ s = false clause

  RStack<Literal*> resLits;

  // Copy the literals from the premise except for the one at `literalPosition`,
  // that has the occurrence of `booleanTerm` replaced with false
  for (Literal* curr : iterTraits(premise->iterLits())) {
    resLits->push( curr != lit 
        ? curr
        : EqHelper::replace(curr, t, troo));
  }

  // Add s = false to the clause
  resLits->push(Literal::createEquality(true, t, fols, AtomicSort::boolSort()));

  return Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::FOOL_PARAMODULATION, premise));
}

ClauseIterator Cases::generateClauses(Clause* premise)
{
  return pvi(premise->getSelectedLiteralIterator()
    .flatMap([this](Literal* lit) {
      return pvi(pushPairIntoRightIterator(lit, EqHelper::getBooleanSubtermIterator(lit, _ord)));
    })
    // filter out top-level terms
    .filter([](pair<Literal*, TermList> arg) {
      auto [lhs, rhs] = arg.first->eqArgs();
      return lhs != arg.second && rhs != arg.second;
    })
    .map([premise](pair<Literal*, TermList> arg) {
      return performCases(premise, arg.first, arg.second);
    }));
}

}
