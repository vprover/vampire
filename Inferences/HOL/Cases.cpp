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
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Cases.hpp"

namespace Inferences {

using namespace std;

template<bool higherOrder>
Cases<higherOrder>::Cases(SaturationAlgorithm& salg) : _ord(salg.getOrdering()) {}

template<bool simplifying>
Clause* performCases(Clause* premise, Literal* lit, Term* t, bool replaceWithTroo)
{
  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());

  // Found a boolean term! Create the C[true] \/ s = false clause

  RStack<Literal*> resLits;

  // Copy the literals from the premise except for `lit`,
  // that has the occurrence of `t` replaced with troo or fols
  for (Literal* curr : iterTraits(premise->iterLits())) {
    resLits->push( curr != lit ? curr : EqHelper::replace(curr, TermList(t), replaceWithTroo ? troo : fols));
  }

  // Add s = false to the clause
  resLits->push(Literal::createEquality(true, TermList(t), replaceWithTroo ? fols : troo, AtomicSort::boolSort()));

  if constexpr (simplifying) {
    return Clause::fromStack(*resLits, SimplifyingInference1(InferenceRule::BOOL_CASES_SIMP, premise));
  } else {
    return Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::BOOL_CASES, premise));
  }
}

template<bool higherOrder>
auto casesFilterFn = [](pair<Literal*, Term*> arg) {
  if constexpr (higherOrder) {
    // TODO consider using iterators that only return booleans
    if (SortHelper::getResultSort(arg.second) != AtomicSort::boolSort()) {
      return false;
    }
    if (HOL::isBool(TermList(arg.second))) {
      return false;
    }
  }
  return true;
};

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
    .filter(casesFilterFn<higherOrder>)
    .map([premise](pair<Literal*, Term*> arg) {
      return performCases</*simplifying=*/false>(premise, arg.first, arg.second, /*replaceWithTroo=*/true);
    }));
}

template class Cases<false>;
template class Cases<true>;

template<bool higherOrder>
Option<ClauseIterator> CasesSimp<higherOrder>::simplifyMany(Clause* premise)
{
  // TODO(HOL): if this is a simplification, we shouldn't perform it on all subterms, just on the first we find.
  auto it = iterTraits(premise->iterLits())
    .flatMap([](Literal* lit) {
      if constexpr (higherOrder) {
        return pvi(pushPairIntoRightIterator(lit, getUniquePersistentIterator(vi(new BooleanSubtermIt(lit)))));
      } else {
        return pvi(pushPairIntoRightIterator(lit, getUniquePersistentIterator(vi(new NonVariableNonTypeIterator(lit)))));
      }
    })
    // filter out top-level terms
    .filter(casesFilterFn<higherOrder>)
    .flatMap([premise](pair<Literal*, Term*> arg) {
      return pvi(iterItems(
        performCases</*simplifying=*/true>(premise, arg.first, arg.second, /*replaceWithTroo=*/true),
        performCases</*simplifying=*/true>(premise, arg.first, arg.second, /*replaceWithTroo=*/false)
      ));
    });

  if (it.hasNext()) {
    return some(pvi(std::move(it)));
  } else {
    return {};
  }
}

template class CasesSimp<false>;
template class CasesSimp<true>;

}
