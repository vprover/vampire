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

template<bool higherOrder>
Cases<higherOrder>::Cases(SaturationAlgorithm& salg) : _ord(salg.getOrdering()) {}

Clause* performCases(Clause* premise, Literal* lit, Term* t)
{
  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());

  // Found a boolean term! Create the C[true] \/ s = false clause

  RStack<Literal*> resLits;

  // Copy the literals from the premise except for the one at `literalPosition`,
  // that has the occurrence of `booleanTerm` replaced with false
  for (Literal* curr : iterTraits(premise->iterLits())) {
    resLits->push( curr != lit 
        ? curr
        : EqHelper::replace(curr, TermList(t), troo));
  }

  // Add s = false to the clause
  resLits->push(Literal::createEquality(true, TermList(t), fols, AtomicSort::boolSort()));

  return Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::FOOL_PARAMODULATION, premise));
}

template<bool higherOrder>
ClauseIterator Cases<higherOrder>::generateClauses(Clause* premise)
{
  return pvi(premise->getSelectedLiteralIterator()
    .flatMap([this](Literal* lit) {
      if constexpr (higherOrder) {
        return pvi(pushPairIntoRightIterator(lit, EqHelper::getRewritableSubtermIterator<BooleanSubtermIt>(lit, _ord)));
      } else {
        return pvi(pushPairIntoRightIterator(lit, EqHelper::getSubtermIterator(lit, _ord, /*higherOrder=*/false)));
      }
    })
    // filter out top-level terms
    .filter([](pair<Literal*, Term*> arg) {
      if constexpr (higherOrder) {
        // TODO consider using an iterator that only returns booleans
        if (SortHelper::getResultSort(arg.second) != TermList(AtomicSort::boolSort())) {
          return false;
        }
      }
      auto [lhs, rhs] = arg.first->eqArgs();
      return lhs != TermList(arg.second) && rhs != TermList(arg.second);
    })
    .map([premise](pair<Literal*, Term*> arg) {
      return performCases(premise, arg.first, arg.second);
    }));
}

template class Cases<false>;
template class Cases<true>;

}
