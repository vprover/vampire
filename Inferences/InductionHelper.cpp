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

#include "Forwards.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Kernel/SortHelper.hpp"
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
  SLQueryResultToTermQueryResultFn(TypedTermList v) : variable(v) {}
  TermLiteralClause operator() (const QueryRes<ResultSubstitutionSP, LiteralClause> slqr) {
    return TermLiteralClause{slqr.unifier->applyToQuery(variable), slqr.data->literal, slqr.data->clause};
  }

  TypedTermList variable;
};

bool isIntegerComparisonLiteral(Literal* lit) {
  if (!lit->ground() || !theory->isInterpretedPredicate(lit)) return false;
  switch (theory->interpretPredicate(lit)) {
    case Theory::INT_LESS:
      // The only supported integer comparison predicate is INT_LESS.
      break;
    case Theory::INT_LESS_EQUAL:
    case Theory::INT_GREATER_EQUAL:
    case Theory::INT_GREATER:
      // All formulas should be normalized to only use INT_LESS and not other integer comparison predicates.

      // Equality proxy may generate useless congruence axioms for the likes of INT_GREATER
      // (although they only appeared in the input and are eliminated by now -> but this also means they are safe to ignore)
      ASS_EQ(env.options->equalityProxy(),Options::EqualityProxy::RSTC);
    default:
      // Not an integer comparison.
      return false;
  }
  return true;
}

};  // namespace

VirtualIterator<TermLiteralClause> InductionHelper::getComparisonMatch(
    bool polarity, bool termIsLeft, Term* t) {
  static unsigned less = env.signature->getInterpretingSymbol(Theory::INT_LESS);
  static TypedTermList var(TermList::var(0), SortHelper::getResultSort(t));
  Literal* pattern = Literal::create2(less, polarity, termIsLeft ? TermList(t) : var, termIsLeft ? var : TermList(t));
  return pvi(getMappingIterator(_comparisonIndex->getUnifications(pattern, /*complementary=*/ false, /*retrieveSubstitution=*/ true),
                                SLQueryResultToTermQueryResultFn(var)));
}

VirtualIterator<TermLiteralClause> InductionHelper::getLess(Term* t)
{
  return pvi(concatIters(
    // x <= t  iff  ~ t < x
    getComparisonMatch(/*polarity=*/false, /*termIsLeft=*/true, t),
    // x < t
    getComparisonMatch(/*polarity=*/true, /*termIsLeft=*/false, t)));
}

VirtualIterator<TermLiteralClause> InductionHelper::getGreater(Term* t)
{
  return pvi(concatIters(
    // x >= t  iff  ~ x < t
    getComparisonMatch(/*polarity=*/false, /*termIsLeft=*/false, t),
    // x > t  iff  t < x
    getComparisonMatch(/*polarity=*/true, /*termIsLeft=*/true, t)));
}

VirtualIterator<QueryRes<ResultSubstitutionSP, TermLiteralClause>> InductionHelper::getTQRsForInductionTerm(Term* inductionTerm) {
  ASS(_inductionTermIndex);
  return _inductionTermIndex->getUnifications(TypedTermList(inductionTerm));
}

bool InductionHelper::isIntegerComparison(Clause* c) {
  if (c->length() != 1) return false;
  return isIntegerComparisonLiteral((*c)[0]);
}

bool InductionHelper::isIntInductionOn() {
  static bool intInd = env.options->induction() == Options::Induction::BOTH ||
                        env.options->induction() == Options::Induction::INTEGER;
  return intInd;
}

bool InductionHelper::isInductionForFiniteIntervalsOn() {
  static bool finite = env.options->integerInductionInterval() == Options::IntegerInductionInterval::FINITE ||
                       env.options->integerInductionInterval() == Options::IntegerInductionInterval::BOTH;
  return isIntInductionOn() && finite;
}

bool InductionHelper::isInductionForInfiniteIntervalsOn() {
  static bool infinite = env.options->integerInductionInterval() == Options::IntegerInductionInterval::INFINITE ||
                         env.options->integerInductionInterval() == Options::IntegerInductionInterval::BOTH;
  return isIntInductionOn() && infinite;
}

bool InductionHelper::isStructInductionOn() {
  static bool structInd = env.options->induction() == Options::Induction::BOTH ||
                          env.options->induction() == Options::Induction::STRUCTURAL;
  return structInd;
}

bool InductionHelper::isNonUnitStructInductionOn() {
  return isStructInductionOn() && env.options->nonUnitInduction();
}

bool InductionHelper::isInductionClause(Clause* c) {
  static Options::InductionChoice kind = env.options->inductionChoice();
  static bool all = (kind == Options::InductionChoice::ALL);
  static bool goal = (kind == Options::InductionChoice::GOAL);
  static bool goal_plus = (kind == Options::InductionChoice::GOAL_PLUS);
  static unsigned maxD = env.options->maxInductionDepth();
  static bool unitOnly = env.options->inductionUnitOnly();
  static bool ansLits = (env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS || env.options->questionAnswering() == Options::QuestionAnsweringMode::PLAIN);
  return ((!unitOnly || c->length()==1 || (c->length() == 2 && ansLits && c->hasAnswerLiteral())) && 
          (all || ( (goal || goal_plus) && c->derivedFromGoal())) &&
                  (maxD == 0 || c->inference().inductionDepth() < maxD)
         );
}

bool InductionHelper::isInductionLiteral(Literal* l) {
  static bool negOnly = env.options->inductionNegOnly();
  return (!negOnly || l->isNegative() ||
          (theory->isInterpretedPredicate(l) && theory->isInequality(theory->interpretPredicate(l)))
         );
}

bool inductionLiteralHasAdmissibleVariables(Literal* l) {
  if (l->getDistinctVars() != 1) {
    return false;
  }
  for (unsigned idx = 0; idx < l->arity(); ++idx) {
    if (l->nthArgument(idx)->isVar()) {
      // NewCNF handles Booleans in some special way, which
      // interferes with our clausification and resolution.
      return SortHelper::getArgSort(l, idx) != AtomicSort::boolSort();
    } else {
      VariableWithSortIterator vi(l->nthArgument(idx)->term());
      if (vi.hasNext()) {
        return vi.next().second != AtomicSort::boolSort();
      }
    }
  }
  ASSERTION_VIOLATION_REP("No variables in a literal which should contain one variable!");
  return true;
}

bool InductionHelper::isNonGroundInductionLiteral(Literal* l) {
  static bool groundOnly = env.options->inductionGroundOnly();
  return (!groundOnly && inductionLiteralHasAdmissibleVariables(l) && isInductionLiteral(l));
}

bool InductionHelper::isInductionTerm(Term* t)
{
  if (!t->ground()) {
    return false;
  }

  static Options::InductionChoice kind = env.options->inductionChoice();
  static bool all = (kind == Options::InductionChoice::ALL);
  static bool goal_plus = (kind == Options::InductionChoice::GOAL_PLUS);
  static bool complexTermsAllowed = env.options->inductionOnComplexTerms();

  auto sym = t->isLiteral()
    ? env.signature->getPredicate(t->functor())
    : env.signature->getFunction(t->functor());
  return (complexTermsAllowed || t->arity()==0) &&
    (all || sym->inGoal() || (goal_plus && sym->inductionSkolem())); // set in NewCNF
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

bool InductionHelper::isStructInductionTerm(Term* t) {
  static bool complexTermsAllowed = env.options->inductionOnComplexTerms();
  return (env.signature->isTermAlgebraSort(SortHelper::getResultSort(t)) &&
           // skip base constructors even if induction on complex terms is on:
          ((complexTermsAllowed && t->arity() != 0) ||
           // otherwise skip all constructors:
           !env.signature->getFunction(t->functor())->termAlgebraCons())
         );
}

Term* InductionHelper::getOtherTermFromComparison(Literal* l, Term* t) {
  if (isIntegerComparisonLiteral(l)) {
    ASS(l->ground());
    ASS_EQ(l->arity(),2);
    for (unsigned i = 0; i < 2; ++i) {
      if (l->termArg(i).term() == t) {
        return l->termArg(1-i).term();
      }
    }
  }
  return nullptr;
}

}  // namespace Inferences
