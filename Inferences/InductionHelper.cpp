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
#include "Kernel/OperatorType.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Signature.hpp"
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

  if (!theory->isInterpretedPredicate(lit)) return false;
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

bool isGroundIntegerComparisonLiteral(Literal* lit) {
  CALL("isGroundIntegerComparisonLiteral");

  if (!lit->ground() || !isIntegerComparisonLiteral(lit)) return false;
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
  return isGroundIntegerComparisonLiteral((*c)[0]);
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

  static const unsigned strictness = 220; //env.options->intInductionStrictness();
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
  if (env.signature->getFunction(f)->fnType()->result() != AtomicSort::intSort() ||
      ((termst >= 1) && theory->isInterpretedConstant(f))) // ||
//      ((termst == 2) && !containsSkolem(tl.term())))
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

SLQueryResultIterator InductionHelper::getStepClauses(Literal* l) {
  return pvi(getConcatenatedIterator(_intIndStepIndex->getGeneralizations(l, true, true),
                                     _intIndStepIndex->getGeneralizations(l, false, true)));
}

SLQueryResultIterator InductionHelper::getBaseClauses(Literal* l) {
  return pvi(getConcatenatedIterator(_intIndBaseIndex->getInstances(l, true, true),
                                     _intIndBaseIndex->getInstances(l, false, true)));
}

bool InductionHelper::isIntInductionThreeOn() {
  CALL("InductionHelper::isIntInductionThreeOn");
  static bool two = env.options->intInduction() == Options::IntInductionKind::THREE ||
                    env.options->intInduction() == Options::IntInductionKind::ALL;
  return isIntInductionOn() && two;
}

bool InductionHelper::isIntInductionThreeGroundOnly() {
  CALL("InductionHelper::isIntInductionThreeGroundOnly");
  static bool ground = true; // TODO(hzzv): change to options
  return ground;
}

bool InductionHelper::isIntBaseCaseTerm(Term* t) {
  CALL("InductionHelper::isIntBaseCaseTerm");
  if (!t->ground()) return false;
  return (env.signature->getFunction(t->functor())->fnType()->result() == AtomicSort::intSort());
}

bool InductionHelper::getIntInductionBaseTerms(Clause* c, vset<Term*>& bases) {
  CALL("InductionHelper::getIntInductionBaseTerms");
  static bool groundOnly = isIntInductionThreeGroundOnly();
  if ((c->length() == 1) && (!groundOnly || (*c)[0]->ground())) {
    NonVariableIterator nvit((*c)[0]);
    while (nvit.hasNext()) {
      TermList tl = nvit.next();
      Term* t = tl.term();
      if (isIntBaseCaseTerm(t) && isIntInductionTermListInLiteral(tl, (*c)[0])) bases.insert(t);
    }
  }
  return !bases.empty();
}

Term* InductionHelper::getBoundTermAndDirection(Literal* l, const TermList& var, bool& upward) {
  CALL("InductionHelper::getBoundTermAndDirection");
  if (!isBoundLiteralWithVar(l, var)) return nullptr;
  upward = (*(l->nthArgument(0)) == var);
  ASS(l->nthArgument(upward)->isTerm());
  return l->nthArgument(upward)->term();
}

bool InductionHelper::isBoundLiteralWithVar(Literal* l, const TermList& var) {
  CALL("InductionHelper::isBoundLiteralWithVar");
  // Bound literal is e.g. "x >= b" (or "x <= b"), which is normalized as "~(x < b)" (or "~(b < x)"), but since
  // it is an antecedent of implication, it is actually "x < b" (or "b < x").
  if (l->isNegative() || !isIntegerComparisonLiteral(l)) return false;
  for (int i = 0; i < 2; ++i) {
    if ((*(l->nthArgument(i)) == var) && l->nthArgument(i^1)->isTerm() && l->nthArgument(i^1)->term()->ground()) return true;
  }
  return false;
}

bool InductionHelper::getIntInductionStepPlusOrMinus(Literal* l1, Literal* l2, const TermList& var, bool& plusOne) {
  RobSubstitution subst;
  SubstIterator sit = subst.matches(l1, 0, l2, 1, true);
  unsigned subCount = 0;
  while (sit.hasNext()) {
    subCount++;
    RobSubstitution* s = sit.next();
    if (s->size() != 1) continue;
    TermList tl = s->apply(var, 0);
    Term* t = tl.term();
    ASS(var != tl); // TODO(hzzv): verify that they are in fact never equal
    unsigned fn = t->functor();
    if (env.signature->getFunction(fn)->fnType()->result() != AtomicSort::intSort()) continue;
    static const TermList posOne(theory->representConstant(IntegerConstantType(1)));
    static const TermList negOne(theory->representConstant(IntegerConstantType(-1)));
    static unsigned plusFn = env.signature->getInterpretingSymbol(Theory::INT_PLUS);
    static unsigned minusFn = env.signature->getInterpretingSymbol(Theory::INT_MINUS);
    ASS(fn != minusFn); // TODO(hzzv): remove this after verifying that INT_MINUS is normalized using unary minus
    Signature::Symbol* fs = env.signature->getFunction(fn);
    if (!fs->interpreted() || (fn != plusFn)) continue;
    for (int j = 0; j < 2; ++j) {
      if ((*t->nthArgument(j^1) == var) && t->nthArgument(j)->isTerm()) {
        plusOne = (*t->nthArgument(j) == posOne);
        if (plusOne || (*t->nthArgument(j) == negOne)) return true;
      }
    }
  }
  ASS(subCount <= 1);
  return false;
}

bool InductionHelper::getIntInductionStepParams(Clause* c, TermList& var, bool& plusOne, int& litIdx, Literal*& bound) {
  CALL("InductionHelper::getIntInductionStepParams");
  unsigned clen = c->length();
  if ((clen > 3) || (clen < 2) || (c->varCnt() != 1)) return false;
  VariableIterator vit((*c)[0]);
  if (!vit.hasNext()) return false;
  var = vit.next();
//  while (vit.hasNext()) ASS(var == vit.next()); // TODO(hzzv): remove this after verifying it always holds
  int stepLits[2] = {0, 1};
  bound = nullptr;
  if (clen == 3) {
    bool foundComparison = false;
    for (int i = 0; i < 3; ++i) {
//      bool isComparison = isIntegerComparisonLiteral((*c)[i]);
//      if (isComparison) {
//        if (foundComparison) return false;
//        foundComparison = true;
        if (isBoundLiteralWithVar((*c)[i], var)) {
          if (foundComparison) return false;
          foundComparison = true;
          stepLits[0] = (i+1)%3;
          stepLits[1] = (i+2)%3;
          bound = (*c)[i];
        } //else return false;
//      }
    }
    if (bound == nullptr) return false;
  }
  for (int i = 0; i < 2; ++i) {
    if (getIntInductionStepPlusOrMinus((*c)[stepLits[i]], (*c)[stepLits[i^1]], var, plusOne)) {
      litIdx = i;
      return true;
    }
  }
  return false;
}

Literal* InductionHelper::getIntInductionStepLiteral(Clause* c) {
  CALL("InductionHelper::getIntInductionStepLiteral");
  TermList var;
  bool plusOne;
  int litIdx;
  Literal* bound;
  if (getIntInductionStepParams(c, var, plusOne, litIdx, bound)) {
    return (*c)[litIdx];
  }
  return nullptr;
}

}  // namespace Inferences
