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
 * Pins how terms print, special terms in particular.
 *
 * There are two printers, reached differently and recursing differently:
 *   - Term::toString, which uses headToString and then Output::interleaved;
 *   - TermList::asArgsToString, a separate stack machine reached from
 *     Literal::toString, which calls headToString on *nested* terms itself and
 *     only re-enters Term::toString for arrow sorts.
 * So every shape below is pinned twice, once under each. Fixing one printer while
 * breaking the other is the failure mode this file exists to catch; the ordinary
 * (non-special) shapes are pinned for the same reason, since a change there would
 * reach every term Vampire prints, HOL applications included.
 */

#include <sstream>

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Parse/TPTP.hpp"
#include "Shell/Options.hpp"

using namespace Kernel;

static const char* PREAMBLE =
  "tff(a_type,type,a: $i).\n"
  "tff(b_type,type,b: $i).\n"
  "tff(d_type,type,d: $i).\n"
  "tff(f_type,type,f: ( $i * $i ) > $i).\n"
  "tff(p_type,type,p: $i > $o).\n"
  "tff(r_type,type,r: $i > $o).\n"
  "tff(s_type,type,s: $o > $o).\n";

/**
 * Parse @b body after the preamble and print its last formula.
 *
 * Always bind the result before asserting on it: ASS_EQ re-evaluates its arguments to
 * build the failure message, and a $let binds a *fresh* symbol, so a second call prints
 * different names and the message contradicts itself.
 */
static std::string printed(const std::string& body)
{
  std::istringstream in(std::string(PREAMBLE) + body);
  Parse::TPTP parser(in, "tTermPrinting");
  parser.parse();
  Unit* last = nullptr;
  UnitList::Iterator it(parser.units());
  while (it.hasNext()) { last = it.next(); }
  ASS(last);
  return last->getFormula()->toString();
}

// An equality argument goes through Term::toString; a predicate argument goes through
// Literal::toString and so through TermList::asArgsToString. Each shape is pinned under
// both, and the two are expected to agree.

TEST_FUN(print_plain_term)
{
  { auto got = printed("tff(t,axiom, d = f(a,b)).\n");
    ASS_EQ(got, "d = f(a,b)"); }
  { auto got = printed("tff(t,axiom, r(f(a,b))).\n");
    ASS_EQ(got, "r(f(a,b))"); }
}

TEST_FUN(print_formula_in_term_position)
{
  { auto got = printed("tff(t,axiom, s(p(a))).\n");
    ASS_EQ(got, "s(p(a))"); }
}

TEST_FUN(print_ite)
{
  { auto got = printed("tff(t,axiom, d = $ite(p(a), a, b)).\n");
    ASS_EQ(got, "d = $ite(p(a),a,b)"); }
  { auto got = printed("tff(t,axiom, r($ite(p(a), a, b))).\n");
    ASS_EQ(got, "r($ite(p(a),a,b))"); }
}

TEST_FUN(print_nested_ite)
{
  { auto got = printed("tff(t,axiom, r($ite(p(a), $ite(p(b), a, b), b))).\n");
    ASS_EQ(got, "r($ite(p(a),$ite(p(b),a,b),b))"); }
}

// one printed() call per test from here on: a $let binds a *fresh* symbol, so a second
// call in the same process would print g1, g2, ... and the expectation would depend on
// how many tests happened to run before it (each TEST_FUN forks, so one call is stable)

TEST_FUN(print_let_under_equality)
{
  { auto got = printed("tff(t,axiom, d = $let(g: $i > $i, g(X) := f(X,X), g(a))).\n");
    ASS_EQ(got, "d = $let(g0: $i > $i,g0(X0) := f(X0,X0),g0(a))"); }
}

TEST_FUN(print_let_under_predicate)
{
  { auto got = printed("tff(t,axiom, r($let(g: $i > $i, g(X) := f(X,X), g(a)))).\n");
    ASS_EQ(got, "r($let(g0: $i > $i,g0(X0) := f(X0,X0),g0(a)))"); }
}

TEST_FUN(print_cond)
{
  { auto got = printed("tff(t,axiom, d = $cond(p(a), a, p(b), b, d)).\n");
    ASS_EQ(got, "d = $cond(p(a),a,p(b),b,d)"); }
  { auto got = printed("tff(t,axiom, r($cond(p(a), a, p(b), b, d))).\n");
    ASS_EQ(got, "r($cond(p(a),a,p(b),b,d))"); }
}

TEST_FUN(print_match)
{
  // $match has no TPTP surface syntax -- SMT-LIB is its only producer -- so build it here
  DECL_SORT(alpha)
  DECL_CONST(u, alpha)
  DECL_CONST(v, alpha)
  DECL_CONST(w, alpha)
  DECL_PRED(rr, {alpha})

  DArray<TermList> args(3);
  args[0] = u.sugaredExpr(); // matched
  args[1] = v.sugaredExpr(); // pattern
  args[2] = w.sugaredExpr(); // body
  TermList t(Term::createMatch(alpha, alpha, 3, args.begin()));

  ASS_EQ(t.toString(), "$match(u,v,w)");
  ASS_EQ(Literal::create1(rr.functor(), true, t)->toString(), "rr($match(u,v,w))");
}

TEST_FUN(print_tuple_let)
{
  // a tuple $let: another head that prints extra material of its own
  env.options->set("newcnf","on"); // the parser refuses tuples otherwise
  // note the binding prints the tuple constructor spelled out while the type uses the
  // bracket sugar -- longstanding, and not something this file is asserting is *good*
  { auto got = printed("tff(t,axiom, d = $let([x: $i, y: $i], [x, y] := [a, b], f(x,y))).\n");
    ASS_EQ(got, "d = $let([x0: $i, y1: $i],tuple2($i,$i,x0,y1) := tuple2($i,$i,a,b),f(x0,y1))"); }
}
