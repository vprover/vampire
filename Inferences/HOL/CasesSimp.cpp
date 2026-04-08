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
 * Implements the inference rule, that is needed for efficient treatment of
 * boolean terms. The details of why it is needed are in the paper
 * "A First Class Boolean Sort in First-Order Theorem Proving and TPTP"
 * by Kotelnikov, Kovacs and Voronkov [1].
 *
 * [1] http://arxiv.org/abs/1505.01682
 */

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "CasesSimp.hpp"

namespace Inferences {

using namespace std;

ClauseIterator performCaseSimp(Clause* premise, Literal* lit, TermList t)
{
  ASS(t.isTerm());

  auto [lhs, rhs] = lit->eqArgs();

  if (t == lhs || t == rhs) {
    return ClauseIterator::getEmpty();
  }

  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());

  Literal* litFols = Literal::createEquality(true, t, fols, AtomicSort::boolSort());
  Literal* litTroo = Literal::createEquality(true, t, troo, AtomicSort::boolSort());

  RStack<Literal*> resLits1;
  RStack<Literal*> resLits2;

  // Copy the literals from the premise except for `lit`,
  // that has the occurrence of `t` replaced with true and false
  for (auto curr : premise->iterLits()) {
    resLits1->push(curr != lit ? curr : EqHelper::replace(curr, t, troo));
    resLits2->push(curr != lit ? curr : EqHelper::replace(curr, t, fols));
  }

  // Add s = false to the clause
  resLits1->push(litFols);
  resLits2->push(litTroo);

  return pvi(iterItems(
    Clause::fromStack(*resLits1, SimplifyingInference1(InferenceRule::CASES_SIMP, premise)),
    Clause::fromStack(*resLits2, SimplifyingInference1(InferenceRule::CASES_SIMP, premise))
  ));
}

Option<ClauseIterator> CasesSimp::simplifyMany(Clause* premise)
{
  auto it = iterTraits(premise->iterLits())
    // TODO aren't all literals equalities in the HOL setting?
    .filter([](Literal* lit){ return lit->isEquality(); })
    .flatMap([](Literal* lit) {
      return pvi(pushPairIntoRightIterator(lit, getUniquePersistentIterator(vi(new BooleanSubtermIt(lit)))));
    })
    .flatMap([premise](pair<Literal*, TermList> arg) {
      return performCaseSimp(premise, arg.first, arg.second);
    });

  if (it.hasNext()) {
    return some(pvi(std::move(it)));
  } else {
    return {};
  }
}

}
