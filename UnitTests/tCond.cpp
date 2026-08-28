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
 * Tests for $cond, the flat chained if/elif/.../else term.
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"

using namespace Kernel;

/** wrap a literal as the $o-sorted term a $cond takes as a condition, as the parser will */
static TermList asCondition(Literal* l)
{ return TermList(Term::createFormula(new AtomicFormula(l))); }

/** $cond(p(X0), a, q(X0), b, c) */
static Term* twoCaseCond(TermList sort, Literal* c1, TermList v1, Literal* c2, TermList v2, TermList e)
{
  DArray<TermList> args(5);
  args[0] = asCondition(c1);
  args[1] = v1;
  args[2] = asCondition(c2);
  args[3] = v2;
  args[4] = e;
  return Term::createCond(sort, 5, args.begin());
}

TEST_FUN(cond_prints_flat)
{
  DECL_DEFAULT_VARS
  DECL_SORT(alpha)
  DECL_CONST(a, alpha)
  DECL_CONST(b, alpha)
  DECL_CONST(c, alpha)
  DECL_PRED(p, {alpha})
  DECL_PRED(q, {alpha})
  DECL_PRED(r, {alpha})

  TermList t(twoCaseCond(alpha, p(x), a.sugaredExpr(), q(x), b.sugaredExpr(), c.sugaredExpr()));

  // Term::toString: head, then the generic argument printer
  ASS_EQ(t.toString(), "$cond(p(X0),a,q(X0),b,c)");

  // Literal::toString reaches the same term through TermList::asArgsToString instead,
  // which is a separate printer -- so it gets its own expectation
  Literal* lit = Literal::create1(r.functor(), true, t);
  ASS_EQ(lit->toString(), "r($cond(p(X0),a,q(X0),b,c))");
}

TEST_FUN(cond_result_sort)
{
  DECL_DEFAULT_VARS
  DECL_SORT(alpha)
  DECL_CONST(a, alpha)
  DECL_CONST(b, alpha)
  DECL_CONST(c, alpha)
  DECL_PRED(p, {alpha})
  DECL_PRED(q, {alpha})

  Term* t = twoCaseCond(alpha, p(x), a.sugaredExpr(), q(x), b.sugaredExpr(), c.sugaredExpr());

  // getResultSort refuses special terms; this is the entry point that handles them
  TermList sort;
  TermList masterVar;
  ALWAYS(SortHelper::getResultSortOrMasterVariable(t, sort, masterVar));
  ASS_EQ(sort, alpha.sugaredExpr());
}

TEST_FUN(cond_to_ite_one_case)
{
  DECL_DEFAULT_VARS
  DECL_SORT(alpha)
  DECL_CONST(a, alpha)
  DECL_CONST(b, alpha)
  DECL_PRED(p, {alpha})

  DArray<TermList> args(3);
  args[0] = asCondition(p(x));
  args[1] = a.sugaredExpr();
  args[2] = b.sugaredExpr();
  Term* t = Term::createCond(alpha, 3, args.begin());

  TermList ite = Term::condToITE(t);
  ASS(ite.isTerm() && ite.term()->isITE());
  ASS_EQ(ite.term()->getSpecialData()->getITECondition()->toString(), "p(X0)");
  ASS_EQ(*ite.term()->nthArgument(0), a.sugaredExpr());
  ASS_EQ(*ite.term()->nthArgument(1), b.sugaredExpr());
  ASS_EQ(ite.term()->getSpecialData()->getSort(), alpha.sugaredExpr());
}

TEST_FUN(cond_to_ite_nests_leftmost_outermost)
{
  DECL_DEFAULT_VARS
  DECL_SORT(alpha)
  DECL_CONST(a, alpha)
  DECL_CONST(b, alpha)
  DECL_CONST(c, alpha)
  DECL_PRED(p, {alpha})
  DECL_PRED(q, {alpha})

  Term* t = twoCaseCond(alpha, p(x), a.sugaredExpr(), q(x), b.sugaredExpr(), c.sugaredExpr());

  // first match wins, so the leftmost condition must end up outermost
  TermList outer = Term::condToITE(t);
  ASS(outer.isTerm() && outer.term()->isITE());
  ASS_EQ(outer.term()->getSpecialData()->getITECondition()->toString(), "p(X0)");
  ASS_EQ(*outer.term()->nthArgument(0), a.sugaredExpr());

  TermList inner = *outer.term()->nthArgument(1);
  ASS(inner.isTerm() && inner.term()->isITE());
  ASS_EQ(inner.term()->getSpecialData()->getITECondition()->toString(), "q(X0)");
  ASS_EQ(*inner.term()->nthArgument(0), b.sugaredExpr());
  ASS_EQ(*inner.term()->nthArgument(1), c.sugaredExpr());
}
