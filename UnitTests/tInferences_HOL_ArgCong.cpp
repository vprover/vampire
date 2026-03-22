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
#include "Inferences/HOL/ArgCong.hpp"

#include "Test/GenerationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_SORT(srt)                                   \
  DECL_SORT_VAR(sx, 0)                             \
  DECL_SORT_VAR(sy, 4)                             \
  DECL_SORT_VAR(sz, 5)                             \
  DECL_VAR_SORTED(x, 0, srt)                       \
  DECL_VAR_SORTED(y, 1, srt)                       \
  DECL_VAR_SORTED(z, 2, srt)                       \
  DECL_VAR_SORTED(xs, 3, arrow({ srt, srt }, srt)) \
  DECL_VAR_SORTED(xs2, 3, sy)                      \
  DECL_VAR_SORTED(ys, 4, arrow(srt, srt))          \
  DECL_VAR_SORTED(zs, 5, arrow(srt, srt))          \
  DECL_PRED(p, { srt })                            \
  DECL_CONST(f, arrow({srt, srt}, srt))            \
  DECL_CONST(g, arrow(srt, srt))                   \
  DECL_POLY_CONST(g2, 1, sx)                       \
  DECL_POLY_CONST(g3, 1, sx)                       \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                \
  DECL_CONST(a, srt)                               \
  DECL_CONST(b, srt)

#define MY_GEN_RULE   ArgCong
#define MY_GEN_TESTER Generation::GenerationTester

// not done for non-selected literals
TEST_GENERATION(fail_1,
    Generation::AsymmetricTest()
      .input( clause({ selected(x == y), g == lam(srt, ap(f, {db0, db0})) }))
      .expected(none())
    )

// not done for negative literals
TEST_GENERATION(fail_2,
    Generation::AsymmetricTest()
      .input( clause({ selected(g != lam(srt, ap(f, {db0, db0}))) }))
      .expected(none())
    )

// not done for functions already applied
TEST_GENERATION(fail_3,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(g, x) == ap(lam(srt, ap(f, {db0, db0})), y)), x == y }))
      .expected(none())
    )

// not done for functions already applied
TEST_GENERATION(fail_4,
    Generation::AsymmetricTest()
      .input( clause({ selected(a == b) }))
      .expected(none())
    )

TEST_GENERATION(success_1,
    Generation::AsymmetricTest()
      .input( clause({ selected(g == lam(srt, ap(f, {x, x}))) }))
      .expected(exactly(clause({ ap(g, y) == ap(lam(srt, ap(f, {x, x})), y) })))
    )

TEST_GENERATION(success_2,
    Generation::AsymmetricTest()
      .input( clause({ selected(g == lam(srt, ap(f, {db0, db0}))), x == y }))
      .expected(exactly(clause({ ap(g, x) == ap(lam(srt, ap(f, {db0, db0})), x), y == z })))
    )

TEST_GENERATION(success_3,
    Generation::AsymmetricTest()
      .input( clause({ selected(g2(sx) == g3(sx)), y == z }))
      .expected(exactly(clause({ ap(g2(arrow(sy, sz)), xs2)  == ap(g3(arrow(sy, sz)), xs2), y == z })))
    )
