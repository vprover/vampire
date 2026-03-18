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
#include "Inferences/HOL/FlexFlexSimplify.hpp"

#include "Test/SimplificationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_SORT(srt)                                   \
  DECL_VAR_SORTED(x, 0, srt)                       \
  DECL_VAR_SORTED(y, 1, srt)                       \
  DECL_VAR_SORTED(z, 2, srt)                       \
  DECL_VAR_SORTED(xs, 3, arrow({ srt, srt }, srt)) \
  DECL_VAR_SORTED(ys, 4, arrow(srt, srt))          \
  DECL_VAR_SORTED(zs, 5, arrow(srt, srt))          \
  DECL_PRED(p, { srt })                            \
  DECL_FUNC(f, {srt, srt}, srt)                    \
  DECL_CONST(g, arrow({srt, srt}, srt))            \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                \
  DECL_CONST(a, srt)                               \
  DECL_CONST(b, srt)

#define MY_SIMPL_RULE   FlexFlexSimplify
#define MY_SIMPL_TESTER Simplification::SimplificationTester

TEST_SIMPLIFY(fail_1,
    Simplification::NotApplicable()
      .input(clause({ x == y }))
    )

TEST_SIMPLIFY(fail_2,
    Simplification::NotApplicable()
      .input(clause({ f(x,y) == x }))
    )

TEST_SIMPLIFY(fail_3,
    Simplification::NotApplicable()
      .input(clause({ f(x,y) != x }))
    )

TEST_SIMPLIFY(fail_4,
    Simplification::NotApplicable()
      .input(clause({ ap(ap(xs,x),y) == f(x,y) }))
    )

TEST_SIMPLIFY(fail_5,
    Simplification::NotApplicable()
      .input(clause({ ap(ap(xs,x),y) == x }))
    )

TEST_SIMPLIFY(fail_6,
    Simplification::NotApplicable()
      .input(clause({ ap(ap(xs,x),y) != x, x == y }))
    )

TEST_SIMPLIFY(fail_7,
    Simplification::NotApplicable()
      .input(clause({ ap(ap(xs,x),y) != x, f(x,z) == z, x != y }))
    )

TEST_SIMPLIFY(fail_10,
    Simplification::NotApplicable()
      .input(clause({ ap(ap(g,x),y) != x }))
    )

TEST_SIMPLIFY(fail_11,
    Simplification::NotApplicable()
      .input(clause({ ap(xs, ap(g, {x, a})) != ys, g != g, ap(ys, a) != ap(zs, ap(lam(srt, db0), b)) }))
    )

TEST_SIMPLIFY(fail_12,
    Simplification::NotApplicable()
      .input(clause({ lam(srt, db0) != ys }))
    )

TEST_SIMPLIFY(success_1,
    Simplification::Success()
      .input(clause({ ap(ap(xs,x),y) != x }))
      .expected(clause({ }))
    )

TEST_SIMPLIFY(success_2,
    Simplification::Success()
      .input(clause({ ap(xs, ap(g, {x, a})) != ys, x != y }))
      .expected(clause({ }))
    )

TEST_SIMPLIFY(success_3,
    Simplification::Success()
      .input(clause({ ap(xs, ap(g, {x, a})) != ys, ap(ys, a) != ap(zs, ap(lam(srt, db0), b)) }))
      .expected(clause({ }))
    )

TEST_SIMPLIFY(success_4,
    Simplification::Success()
      .input(clause({ lam(srt, x) != ys }))
      .expected(clause({ }))
    )
