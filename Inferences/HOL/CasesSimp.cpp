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
 * @file CasesSimp.cpp
 * Higher-order, simplifying variant of FOOL paramodulation.
 * @see Cases and FOOLParamodulation classes.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "CasesSimp.hpp"

namespace Inferences {

using namespace std;

Clause* performCaseSimp(Clause* premise, Literal* lit, TermList t, bool replaceWithTroo)
{
  ASS(t.isTerm());

  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());

  auto newLit = Literal::createEquality(true, t,
    replaceWithTroo ? fols : troo, AtomicSort::boolSort());

  RStack<Literal*> resLits;

  // Copy the literals from the premise except for `lit`,
  // that has the occurrence of `t` replaced with troo or fols
  for (auto curr : premise->iterLits()) {
    resLits->push(curr != lit ? curr : EqHelper::replace(curr, t, replaceWithTroo ? troo : fols));
  }

  // Add new lit to the clause
  resLits->push(newLit);

  return Clause::fromStack(*resLits, SimplifyingInference1(InferenceRule::CASES_SIMP, premise));
}

Option<ClauseIterator> CasesSimp::simplifyMany(Clause* premise)
{
  // TODO if this is a simplification, we shouldn't perform it on all subterms, just on the first we find.
  auto it = iterTraits(premise->iterLits())
    // TODO aren't all literals equalities in the HOL setting?
    .filter([](Literal* lit){ return lit->isEquality(); })
    .flatMap([](Literal* lit) {
      return pvi(pushPairIntoRightIterator(lit, getUniquePersistentIterator(vi(new BooleanSubtermIt(lit)))));
    })
    // filter out top-level terms
    .filter([](pair<Literal*, TermList> arg) {
      auto [lhs, rhs] = arg.first->eqArgs();
      return lhs != arg.second && rhs != arg.second;
    })
    .flatMap([premise](pair<Literal*, TermList> arg) {
      return pvi(iterItems(
        performCaseSimp(premise, arg.first, arg.second, true),
        performCaseSimp(premise, arg.first, arg.second, false)
      ));
    });

  if (it.hasNext()) {
    return some(pvi(std::move(it)));
  } else {
    return {};
  }
}

}
