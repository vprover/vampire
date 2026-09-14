/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Test/SyntaxSugar.hpp"
#include "Inferences/HOL/BetaEtaSimplify.hpp"

#include "Test/SimplificationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_SORT(srt)                                   \
  DECL_VAR_SORTED(x, 0, srt)                       \
  DECL_VAR_SORTED(y, 1, srt)                       \
  DECL_VAR_SORTED(z, 2, srt)                       \
  DECL_VAR_SORTED(xs, 3, arrow({ srt, srt }, srt)) \
  DECL_FUNC(f, {srt, srt}, srt)                    \
  DECL_CONST(g, arrow({srt, srt}, srt))            \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                \
  DECL_DE_BRUIJN_INDEX(db1, 1, srt)                \
  DECL_CONST(a, srt)                               \
  DECL_CONST(b, srt)

#define MY_SIMPL_RULE   BetaEtaSimplify
#define MY_SIMPL_TESTER Simplification::SimplificationTester

TEST_SIMPLIFY(fail_1,
    Simplification::NotApplicable()
      .input(clause({ x == y, f(x,y) != x }))
    )

TEST_SIMPLIFY(success_1,
    Simplification::Success()
      .input(clause({ ap(lam(srt, lam(srt, ap(g, {db1, db0}))), {a, b}) != ap(lam(srt, ap(g, db0)), {f(x,y), b}) }))
      .expected(clause({ ap(g, {a, b}) != ap(g, {f(x,y), b}) }))
    )

TEST_SIMPLIFY(success_2,
    Simplification::Success()
      .input(clause({ f(x,y) == a, ap(lam(srt, ap(lam(srt, ap(g, db0)), db0)), a) != ap(lam(srt, ap(xs, z)), b) }))
      .expected(clause({ f(x,y) == a, ap(g, a) != ap(xs, z) }))
    )
