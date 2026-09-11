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

#include <sstream>

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Exception.hpp"
#include "Parse/TPTP.hpp"

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

// ----------------------------------------------------------------------------
// the TPTP frontend

/** the type declarations the $cond snippets below are read against */
static const char* PREAMBLE =
  "tff(alpha_type,type,alpha: $tType).\n"
  "tff(a_type,type,a: alpha).\n"
  "tff(b_type,type,b: alpha).\n"
  "tff(c_type,type,c: alpha).\n"
  "tff(d_type,type,d: alpha).\n"
  "tff(p_type,type,p: alpha > $o).\n"
  "tff(q_type,type,q: alpha > $o).\n";

static UnitList* parseTPTP(const std::string& body)
{
  std::istringstream in(std::string(PREAMBLE) + body);
  Parse::TPTP parser(in, "tCond");
  parser.parse();
  return parser.units();
}

/** the last unit parsed, printed */
static std::string lastFormula(UnitList* us)
{
  Unit* last = nullptr;
  UnitList::Iterator it(us);
  while (it.hasNext()) { last = it.next(); }
  ASS(last);
  return last->getFormula()->toString();
}

TEST_FUN(cond_parses_and_prints_back)
{
  // what the printer emits must be what the parser accepts -- that round trip is
  // the whole point of having a flat form, since --mode model_check reads it back
  UnitList* us = parseTPTP("tff(t,axiom, d = $cond(p(d), a, q(d), b, c)).\n");
  ASS_EQ(lastFormula(us), "d = $cond(p(d),a,q(d),b,c)");
}

TEST_FUN(cond_parses_in_formula_position)
{
  UnitList* us = parseTPTP("tff(t,axiom, $cond(p(d), q(d), $false)).\n");
  ASS_EQ(lastFormula(us), "$cond(p(d),q(d),$false)");
}

TEST_FUN(cond_parses_a_compound_condition)
{
  // a condition needs no sub-grammar of its own: TERM_INFIX routes the connectives
  // through FORMULA_INSIDE_TERM, which is exactly the $o-sorted term $cond wants
  UnitList* us = parseTPTP("tff(t,axiom, d = $cond(p(d) & ~q(d), a, b)).\n");
  ASS_EQ(lastFormula(us), "d = $cond(p(d) & ~q(d),a,b)");
}

TEST_FUN(cond_parses_conditions_of_argument_equalities)
{
  // the shape FMB model printing will emit for a conditional-flip layer, and no
  // parentheses needed around the conditions any more: the parser no longer ends a
  // term at a connective that follows an equality, nor carries the equality-argument
  // guard into a nested argument list (checks/parse/term-eq-connective.p covers both
  // in their own right). The parenthesized spelling must read the same, so both are here
  // (kept ground: printing a sorted quantifier needs env.initiallyHasNonDefaultSorts(),
  // which only real input sets -- checks/parse/cond.p covers the quantified version)
  UnitList* bare = parseTPTP(
    "tff(g_type,type,g: ( alpha * alpha ) > alpha).\n"
    "tff(t,axiom, g(d,d) = $cond(d = a & d = b, c, d = a, b, a)).\n");
  ASS_EQ(lastFormula(bare), "g(d,d) = $cond(d = a & d = b,c,d = a,b,a)");

  UnitList* parens = parseTPTP(
    "tff(g_type,type,g: ( alpha * alpha ) > alpha).\n"
    "tff(t,axiom, g(d,d) = $cond((d = a & d = b), c, (d = a), b, a)).\n");
  ASS_EQ(lastFormula(parens), "g(d,d) = $cond(d = a & d = b,c,d = a,b,a)");
}

TEST_FUN(cond_keeps_a_conjunct_before_an_equality)
{
  // "A & B = C" as a condition used to lose its "A &" silently -- a formula-level bug
  // that the guard suspension exposed inside $cond, fixed on the parser side
  UnitList* us = parseTPTP("tff(t,axiom, $cond(p(d) & q(d) = $true, p(d), $true)).\n");
  ASS_EQ(lastFormula(us), "$cond(p(d) & (q(d) = $true),p(d),$true)");
}

/** did parsing @b body fail with a user error? */
static bool rejected(const std::string& body)
{
  try {
    parseTPTP(body);
    return false;
  } catch (UserErrorException&) {
    return true;
  }
}

TEST_FUN(cond_rejects_an_even_number_of_arguments)
{
  // no else branch
  ASS(rejected("tff(t,axiom, d = $cond(p(d), a, q(d), b)).\n"));
}

TEST_FUN(cond_rejects_too_few_arguments)
{
  ASS(rejected("tff(t,axiom, d = $cond(a)).\n"));
}

TEST_FUN(cond_rejects_a_non_boolean_condition)
{
  ASS(rejected("tff(t,axiom, d = $cond(a, b, c)).\n"));
}

TEST_FUN(cond_rejects_mismatched_branch_sorts)
{
  ASS(rejected("tff(t,axiom, d = $cond(p(d), a, $true)).\n"));
}
