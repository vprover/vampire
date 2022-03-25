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
  if (_splitter) _splitter->onNewClause(c);
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

bool InductionHelper::isIntInductionTermListInLiteral(TermList& tl, Literal* l) {
  CALL("InductionHelper::isIntInductionTermInLiteral");

  ASS(tl.isTerm());
  // Term tl has to be an integer term, and not an interpreted constant.
  unsigned f = tl.term()->functor();
  // TODO: move this check to later (when we know the bounds)
  if ((env.signature->getFunction(f)->fnType()->result() != AtomicSort::intSort()) ||
      theory->isInterpretedConstant(f))
  {
    return false;
  }
  // Integer term tl from literal l cannot be used for induction if l is an integer
  // comparison and tl is one of the comparison's arguments.
  if (isIntegerComparisonLiteral(l) &&
      ((tl == *l->nthArgument(0)) || (tl == *l->nthArgument(1)))) {
    return false;
  }
  return true;
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
