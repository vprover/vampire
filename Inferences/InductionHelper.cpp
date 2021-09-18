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
 * @file Induction.cpp
 * Implements class Induction.
 */

#include "Indexing/Index.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Theory.hpp"

#include "Shell/Options.hpp"

#include "InductionHelper.hpp"

namespace Inferences {

namespace {

struct SLQueryResultToTermQueryResultFn
{
  SLQueryResultToTermQueryResultFn(TermList v) : variable(v) {}
  TermQueryResult operator() (const SLQueryResult slqr) {
    return TermQueryResult(slqr.substitution->applyToQuery(variable), slqr.literal, slqr.clause);
  }

  TermList variable;
};

bool isIntegerComparisonLiteral(Literal* lit) {
  CALL("isIntegerComparisonLiteral");

  if (!lit->ground() || !theory->isInterpretedPredicate(lit)) return false;
  switch (theory->interpretPredicate(lit)) {
    case Theory::INT_LESS:
      // The only supported integer comparison predicate is INT_LESS.
      break;
    case Theory::INT_LESS_EQUAL:
    case Theory::INT_GREATER_EQUAL:
    case Theory::INT_GREATER:
      // All formulas should be normalized to only use INT_LESS and not other integer comparison predicates.
      ASSERTION_VIOLATION;
    default:
      // Not an integer comparison.
      return false;
  }
  return true;
}

};  // namespace

TermQueryResultIterator InductionHelper::getComparisonMatch(
    bool polarity, TermList& left, TermList& right, TermList& var) {
  CALL("InductionHelper::getComparisonMatch");

  static unsigned less = env.signature->getInterpretingSymbol(Theory::INT_LESS);

  Literal* pattern = Literal::create2(less, polarity, left, right);
  return pvi(getMappingIterator(_comparisonIndex->getUnifications(pattern, /*complementary=*/ false, /*retrieveSubstitution=*/ true),
                                SLQueryResultToTermQueryResultFn(var)));
}

TermQueryResultIterator InductionHelper::getLessEqual(Term* t)
{
  CALL("InductionHelper::getLessEqual");

  static TermList var(0, false);
  TermList tl(t);
  // x <= t  iff  ~ t < x
  return getComparisonMatch(/*polarity=*/false, tl, var, var);
}
TermQueryResultIterator InductionHelper::getLess(Term* t)
{
  CALL("InductionHelper::getLess");

  static TermList var(0, false);
  TermList tl(t);
  // x < t
  return getComparisonMatch(/*polarity=*/true, var, tl, var);
}
TermQueryResultIterator InductionHelper::getGreaterEqual(Term* t)
{
  CALL("InductionHelper::getGreaterEqual");

  static TermList var(0, false);
  TermList tl(t);
  // x >= t  iff  ~ x < t
  return getComparisonMatch(/*polarity=*/false, var, tl, var);
}
TermQueryResultIterator InductionHelper::getGreater(Term* t)
{
  CALL("InductionHelper::getGreater");

  static TermList var(0, false);
  TermList tl(t);
  // x > t  iff  t < x
  return getComparisonMatch(/*polarity=*/true, tl, var, var);
}

TermQueryResultIterator InductionHelper::getTQRsForInductionTerm(TermList inductionTerm) {
  CALL("InductionHelper::getIndTQRsForInductionTerm");

  ASS(_inductionTermIndex);
  return _inductionTermIndex->getUnifications(inductionTerm);
}

void InductionHelper::callSplitterOnNewClause(Clause* c) {
  CALL("InductionHelper::callSplitterOnNewClause");
  static bool splitting = env.options->splitting();
  if (splitting) _splitter->onNewClause(c);
}

bool InductionHelper::isIntegerComparison(Clause* c) {
  CALL("InductionHelper::isIntegerComparison");
  if (c->length() != 1) return false;
  return isIntegerComparisonLiteral((*c)[0]);
}

bool InductionHelper::isIntInductionOn() {
  CALL("InductionHelper::isIntInductionOn");
  static bool intInd = env.options->induction() == Options::Induction::BOTH ||
                        env.options->induction() == Options::Induction::INTEGER;
  return intInd;
}

bool InductionHelper::isIntInductionOneOn() {
  CALL("InductionHelper::isIntInductionOneOn");
  static bool one = env.options->intInduction() == Options::IntInductionKind::ONE ||
                    env.options->intInduction() == Options::IntInductionKind::ALL;
  return isIntInductionOn() && one;
}

bool InductionHelper::isIntInductionTwoOn() {
  CALL("InductionHelper::isIntInductionTwoOn");
  static bool two = env.options->intInduction() == Options::IntInductionKind::TWO ||
                    env.options->intInduction() == Options::IntInductionKind::ALL;
  return isIntInductionOn() && two;
}

bool InductionHelper::isInductionForFiniteIntervalsOn() {
  CALL("InductionHelper::isInductionForFiniteIntervalsOn");
  static bool finite = env.options->integerInductionInterval() == Options::IntegerInductionInterval::FINITE ||
                       env.options->integerInductionInterval() == Options::IntegerInductionInterval::BOTH;
  return isIntInductionOn() && finite;
}

bool InductionHelper::isInductionForInfiniteIntervalsOn() {
  CALL("InductionHelper::isInductionForInfiniteIntervalsOn");
  static bool infinite = env.options->integerInductionInterval() == Options::IntegerInductionInterval::INFINITE ||
                         env.options->integerInductionInterval() == Options::IntegerInductionInterval::BOTH;
  return isIntInductionOn() && infinite;
}

bool InductionHelper::isStructInductionOn() {
  CALL("InductionHelper::isStructInductionOn");
  static bool structInd = env.options->induction() == Options::Induction::BOTH ||
                          env.options->induction() == Options::Induction::STRUCTURAL;
  return structInd;
}

bool InductionHelper::isStructInductionOneOn() {
  CALL("InductionHelper::isStructInductionOneOn");
  static bool structInd = env.options->structInduction() == Options::StructuralInductionKind::ALL ||
                          env.options->structInduction() == Options::StructuralInductionKind::ONE;
  return structInd;
}

bool InductionHelper::isStructInductionRecDefOn() {
  CALL("InductionHelper::isStructInductionRecDefOn");
  static bool structInd = env.options->structInduction() == Options::StructuralInductionKind::ALL ||
                          env.options->structInduction() == Options::StructuralInductionKind::REC_DEF;
  return structInd;
}

bool InductionHelper::isInductionClause(Clause* c) {
  CALL("InductionHelper::isInductionClause");
  static Options::InductionChoice kind = env.options->inductionChoice();
  static bool all = (kind == Options::InductionChoice::ALL);
  static bool goal = (kind == Options::InductionChoice::GOAL);
  static bool goal_plus = (kind == Options::InductionChoice::GOAL_PLUS);
  static unsigned maxD = env.options->maxInductionDepth();
  static bool unitOnly = env.options->inductionUnitOnly();
  return ((!unitOnly || c->length()==1) && 
          (all || ( (goal || goal_plus) && c->derivedFromGoal())) &&
                  (maxD == 0 || c->inference().inductionDepth() < maxD)
         );
}

bool InductionHelper::isInductionLiteral(Literal* l) {
  CALL("InductionHelper::isInductionLiteral");
  static bool negOnly = env.options->inductionNegOnly();
  return ((!negOnly || l->isNegative() || 
           (theory->isInterpretedPredicate(l) && theory->isInequality(theory->interpretPredicate(l))) ||
           isIntegerComparisonLiteral(l) // we allow comparison literals, since we cannot decide whether they are negative
          ) && l->ground()
         );
}

bool InductionHelper::isSideLiteral(Literal* l, Clause* c) {
  CALL("InductionHelper::isSideLiteral");
  return l->ground() &&
    (!c->inference().inductionDepth() ||
    (!l->isEquality() && InductionHelper::isInductionLiteral(l, c)));
}

bool InductionHelper::isMainSidePair(Literal* main, Clause* mainCl, Literal* side, Clause* sideCl) {
  if (!side->ground()) return false;
  auto mainSk = Inferences::InductionHelper::collectInductionSkolems(main, mainCl);
  auto sideSk = Inferences::InductionHelper::collectInductionSkolems(side, sideCl);
  return // either they are both induction depth 0 (not yet inducted on)
         ((!mainCl->inference().inductionDepth() && !sideCl->inference().inductionDepth()) ||
         // or they are non-equality hypothesis and conclusion from the same step
         (!side->isEquality() && !main->isEquality() && !mainSk.empty() && !sideSk.empty() &&
          includes(mainSk.begin(), mainSk.end(), sideSk.begin(), sideSk.end())));
}

bool InductionHelper::isInductionLiteral(Literal* l, Clause* cl) {
  CALL("InductionHelper::isInductionLiteral");
  auto info = cl->inference().inductionInfo();
  if (l->ground() && info && !info->isEmpty()) {
    NonVariableIterator nvi(l);
    while (nvi.hasNext()) {
      unsigned fn = nvi.next().term()->functor();
      if (info->find(fn)) {
        return true;
      }
    }
  }
  return false;
}

vset<unsigned> InductionHelper::collectInductionSkolems(Literal* l, Clause* cl) {
  return collectInductionSkolems(l, cl->inference().inductionInfo());
}

vset<unsigned> InductionHelper::collectInductionSkolems(Literal* l, const DHSet<unsigned>* info) {
  CALL("InductionHelper::collectInductionSkolems");
  vset<unsigned> res;
  if (l->ground() && info && !info->isEmpty()) {
    NonVariableIterator nvi(l);
    while (nvi.hasNext()) {
      unsigned fn = nvi.next().term()->functor();
      if (info->find(fn)) {
        res.insert(fn);
      }
    }
  }
  return res;
}

bool InductionHelper::isInductionTermFunctor(unsigned f) {
  CALL("InductionHelper::isInductionTermFunctor");
  static Options::InductionChoice kind = env.options->inductionChoice();
  static bool all = (kind == Options::InductionChoice::ALL);
  static bool goal_plus = (kind == Options::InductionChoice::GOAL_PLUS);
  static bool complexTermsAllowed = env.options->inductionOnComplexTerms();
  return ((complexTermsAllowed || env.signature->functionArity(f)==0) &&
          (all ||
           env.signature->getFunction(f)->inGoal() ||
           (goal_plus && env.signature->getFunction(f)->inductionSkolem()) // set in NewCNF
          )
         );
}

bool containsSkolem(Term* t) {
  if (env.signature->getFunction(t->functor())->skolem()) return true; 
  NonVariableIterator nvi(t);
  while (nvi.hasNext()) {
    if (env.signature->getFunction(nvi.next().term()->functor())->skolem()) return true;
  }
  return false;
}

bool termAndLiteralSatisfyStrictness(const TermList& tl, Literal* l, unsigned strictness) {
  if (((strictness == 1) &&
       (((tl == *l->nthArgument(0)) && !l->nthArgument(1)->containsSubterm(tl)) ||
        ((tl == *l->nthArgument(1)) && !l->nthArgument(0)->containsSubterm(tl)))) ||
      ((strictness == 2) && (l->countSubtermOccurrences(tl) < 2)) || 
      ((strictness == 3) &&
       (!l->nthArgument(0)->containsSubterm(tl) || !l->nthArgument(1)->containsSubterm(tl))) || 
      (strictness == 4)) {
    return false;
  }
  return true;
}

bool InductionHelper::isIntInductionTermListInLiteral(TermList& tl, Literal* l) {
  CALL("InductionHelper::isIntInductionTermInLiteral");

  static const unsigned strictness = env.options->intInductionStrictness();
  static const unsigned termst = strictness % 10;
  static const unsigned compst = (strictness / 10) % 10;
  static const unsigned eqst = (strictness / 100) % 10;
  ASS(termst < 3);
  ASS(compst < 5);
  ASS(eqst < 5);

  // Term tl has to be an integer term, and not an interpreted constant.
  // Further, integer term tl from literal l cannot be used for induction if any
  // of the following conditions is not satisfied.
  // Term strictness (applies on any tl):
  //   1: tl is an interpreted constant
  //   2: tl does not contain a skolem function
  // Comparison or equality strictness (applies when l is a comparison or an equality):
  //   1: tl is a top-level argument of l, but it does not occur in the other argument of l
  //   2: t has only one occurrence in l
  //   3: t does not occur in both arguments of l
  //   4: comparisons or equalities are not allowed
  ASS(tl.isTerm());
  unsigned f = tl.term()->functor();
  if (env.signature->getFunction(f)->fnType()->result() != Term::intSort() ||
      ((termst >= 1) && theory->isInterpretedConstant(f)) ||
      ((termst == 2) && !containsSkolem(tl.term())))
  {
    return false;
  }
  const bool isEquality = (theory->isInterpretedPredicate(l) && l->isEquality());
  if ((isEquality && !termAndLiteralSatisfyStrictness(tl, l, eqst)) ||
      (!isEquality && isIntegerComparisonLiteral(l) && !termAndLiteralSatisfyStrictness(tl, l, compst))) {
    return false;
  }
  return true;
}

bool InductionHelper::isIntegerBoundLiteral(const TermList& tl, Literal* l) {
  return isIntegerComparisonLiteral(l) &&
    (((tl == *l->nthArgument(0)) && !l->nthArgument(1)->containsSubterm(tl)) ||
     ((tl == *l->nthArgument(1)) && !l->nthArgument(0)->containsSubterm(tl)));
}

bool InductionHelper::isStructInductionFunctor(unsigned f) {
  CALL("InductionHelper::isStructInductionFunctor");
  static bool complexTermsAllowed = env.options->inductionOnComplexTerms();
  return (env.signature->isTermAlgebraSort(env.signature->getFunction(f)->fnType()->result())  &&
           // skip base constructors even if induction on complex terms is on:
          ((complexTermsAllowed && env.signature->functionArity(f) != 0) ||
           // otherwise skip all constructors:
           !env.signature->getFunction(f)->termAlgebraCons())
         );
}

bool InductionHelper::isStructInductionTerm(Term* t) {
  CALL("InductionHelper::isStructInductionTerm");
  if (!isInductionTermFunctor(t->functor()) || !isStructInductionFunctor(t->functor())) {
    return false;
  }
  if (!t->arity() || !env.options->inductionOnComplexTerms()) {
    return true;
  }
  NonVariableIterator nvi(t);
  while (nvi.hasNext()) {
    auto st = nvi.next().term();
    if (!st->arity() &&
      (!env.signature->isTermAlgebraSort(env.signature->getFunction(st->functor())->fnType()->result()) ||
        !env.signature->getFunction(st->functor())->termAlgebraCons()))
    {
      return true;
    }
  }
  return false;
}

TermList* InductionHelper::getLowerBoundForTermListFromLiteral(const TermList& tl, Literal* l) {
  ASS(isIntegerComparisonLiteral(l));
  if (l->isPositive()) {
    // 'l' should be 'bound < tl'
    if (tl == *l->nthArgument(1)) return l->nthArgument(0);
  } else {
    // 'l' should be '~ tl < bound' (equiv. to 'bound <= tl')
    if (tl == *l->nthArgument(0)) return l->nthArgument(1);
  }
  return nullptr;
}

TermList* InductionHelper::getUpperBoundForTermListFromLiteral(const TermList& tl, Literal* l) {
  ASS(isIntegerComparisonLiteral(l));
  if (l->isPositive()) {
    // 'l' should be 'tl < bound'
    if (tl == *l->nthArgument(0)) return l->nthArgument(1);
  } else {
    // 'l' should be '~ bound < tl' (equiv. to 'tl <= bound')
    if (tl == *l->nthArgument(1)) return l->nthArgument(0);
  }
  return nullptr;
}

}  // namespace Inferences
