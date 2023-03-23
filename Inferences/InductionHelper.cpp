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
#include "Kernel/OperatorType.hpp"
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
    return TermQueryResult(slqr.unifier->applyToQuery(variable), slqr.literal, slqr.clause, ResultSubstitutionSP());
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
    bool polarity, bool termIsLeft, Term* t) {
  CALL("InductionHelper::getComparisonMatch");

  static unsigned less = env.signature->getInterpretingSymbol(Theory::INT_LESS);
  static TermList var(0, false);
  Literal* pattern = Literal::create2(less, polarity, termIsLeft ? TermList(t) : var, termIsLeft ? var : TermList(t));
  return pvi(getMappingIterator(_comparisonIndex->getUnifications(pattern, /*complementary=*/ false, /*retrieveSubstitution=*/ true),
                                SLQueryResultToTermQueryResultFn(var)));
}

TermQueryResultIterator InductionHelper::getLess(Term* t)
{
  CALL("InductionHelper::getLess");
  return pvi(getConcatenatedIterator(
    // x <= t  iff  ~ t < x
    getComparisonMatch(/*polarity=*/false, /*termIsLeft=*/true, t),
    // x < t
    getComparisonMatch(/*polarity=*/true, /*termIsLeft=*/false, t)));
}

TermQueryResultIterator InductionHelper::getGreater(Term* t)
{
  CALL("InductionHelper::getGreater");
  return pvi(getConcatenatedIterator(
    // x >= t  iff  ~ x < t
    getComparisonMatch(/*polarity=*/false, /*termIsLeft=*/false, t),
    // x > t  iff  t < x
    getComparisonMatch(/*polarity=*/true, /*termIsLeft=*/true, t)));
}

TermQueryResultIterator InductionHelper::getTQRsForInductionTerm(Term* inductionTerm) {
  CALL("InductionHelper::getIndTQRsForInductionTerm");

  ASS(_inductionTermIndex);
  return _inductionTermIndex->getUnifications(TypedTermList(inductionTerm));
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
  return isIntInductionOn() && (env.options->intInduction() == Options::IntInductionKind::ONE);
}

bool InductionHelper::isIntInductionTwoOn() {
  CALL("InductionHelper::isIntInductionTwoOn");
  return isIntInductionOn() && (env.options->intInduction() == Options::IntInductionKind::TWO);
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

bool InductionHelper::isNonUnitStructInductionOn() {
  CALL("InductionHelper::isNonUnitStructInductionOn");
  return isStructInductionOn() && env.options->nonUnitInduction();
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
           (theory->isInterpretedPredicate(l) && theory->isInequality(theory->interpretPredicate(l)))
          ) && l->ground()
         );
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

static bool containsSkolem(Term* t) {
  unsigned f = t->functor();
  // Special case: t is a non-complex term (the most common case in induction)
  if (env.signature->functionArity(f) == 0) {
    return env.signature->getFunction(f)->skolem();
  }
  // If t is complex, we iterate through all its non-variable subterms including itself
  NonVariableIterator nvi(t, true);
  while (nvi.hasNext()) {
    if (env.signature->getFunction(nvi.next().term()->functor())->skolem()) return true;
  }
  return false;
}

static bool termAndLiteralSatisfyStrictness(const TermList& tl, Literal* l, Options::IntegerInductionLiteralStrictness strictness) {
  using LS = Options::IntegerInductionLiteralStrictness;
  switch(strictness) {
  case LS::NONE:
    return true;
  case LS::TOPLEVEL_NOT_IN_OTHER:
    return
      !(((tl == *l->nthArgument(0)) && !l->nthArgument(1)->containsSubterm(tl)) ||
        ((tl == *l->nthArgument(1)) && !l->nthArgument(0)->containsSubterm(tl)));
  case LS::ONLY_ONE_OCCURRENCE:
    return !(l->countSubtermOccurrences(tl) < 2);
  case LS::NOT_IN_BOTH:
    return !(!l->nthArgument(0)->containsSubterm(tl) || !l->nthArgument(1)->containsSubterm(tl));
  case LS::ALWAYS:
    return false;
  default:
    ASSERTION_VIOLATION
  }
}

bool InductionHelper::isIntInductionTermListInLiteral(Term* tl, Literal* l) {
  CALL("InductionHelper::isIntInductionTermInLiteral");

  // Term tl has to be an integer term.
  // Further, integer term tl from literal l cannot be used for induction if any
  // of the following conditions is satisfied.
  // Term strictness (applies on any tl):
  //   1: tl is an interpreted constant
  //   2: tl does not contain a skolem function
  // Comparison or equality strictness (applies when l is a comparison or an equality):
  //   1: tl is a top-level argument of l, but it does not occur in the other argument of l
  //   2: tl has only one occurrence in l
  //   3: tl does not occur in both arguments of l
  //   4: comparisons or equalities are not allowed
  unsigned f = tl->functor();
  if (env.signature->getFunction(f)->fnType()->result() != AtomicSort::intSort())
    return false;

  using TS = Options::IntegerInductionTermStrictness;
  switch(env.options->integerInductionStrictnessTerm()) {
  case TS::NONE:
    break;
  case TS::INTERPRETED_CONSTANT:
    if(theory->isInterpretedConstant(f))
      return false;
    break;
  case TS::NO_SKOLEMS:
    if(!containsSkolem(tl))
      return false;
    break;
  }

  return (l->isEquality()
    ? termAndLiteralSatisfyStrictness(TermList(tl), l, env.options->integerInductionStrictnessEq())
    : !isIntegerComparisonLiteral(l) ||
      termAndLiteralSatisfyStrictness(TermList(tl), l, env.options->integerInductionStrictnessComp()));
}

bool InductionHelper::isStructInductionFunctor(unsigned f) {
  CALL("InductionHelper::isStructInductionFunctor");
  static bool complexTermsAllowed = env.options->inductionOnComplexTerms();
  return (env.signature->isTermAlgebraSort(env.signature->getFunction(f)->fnType()->result()) &&
           // skip base constructors even if induction on complex terms is on:
          ((complexTermsAllowed && env.signature->functionArity(f) != 0) ||
           // otherwise skip all constructors:
           !env.signature->getFunction(f)->termAlgebraCons())
         );
}

}  // namespace Inferences
