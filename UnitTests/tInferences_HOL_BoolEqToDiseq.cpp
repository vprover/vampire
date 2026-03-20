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
#include "Inferences/HOL/BoolEqToDiseq.hpp"

#include "Test/GenerationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_SORT(srt)                                   \
  DECL_SORT_BOOL                                   \
  TROO                                             \
  FOLS                                             \
  DECL_NOT_PROXY                                   \
  DECL_VAR_SORTED(x, 0, srt)                       \
  DECL_VAR_SORTED(y, 1, srt)                       \
  DECL_VAR_SORTED(z, 2, srt)                       \
  DECL_VAR_SORTED(xs, 3, Bool)                     \
  DECL_VAR_SORTED(ys, 4, Bool)                     \
  DECL_CONST(f, arrow(srt, Bool))                  \
  DECL_CONST(g, arrow(srt, srt))                   \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                \
  DECL_CONST(a, Bool)                              \
  DECL_CONST(b, Bool)                              \
  DECL_CONST(c, srt)

#define MY_GEN_RULE   BoolEqToDiseq
#define MY_GEN_TESTER Generation::GenerationTester

// not done for non-bool literals
TEST_GENERATION(fail_1,
    Generation::AsymmetricTest()
      .input( clause({ c == x }))
      .expected(none())
    )

TEST_GENERATION(fail_2,
    Generation::AsymmetricTest()
      .input( clause({ ap(g, x) == ap(g, c) }))
      .expected(none())
    )

// not done for negative literals
TEST_GENERATION(fail_3,
    Generation::AsymmetricTest()
      .input( clause({ a != xs }))
      .expected(none())
    )

// not done for not-proxy terms
TEST_GENERATION(fail_4,
    Generation::AsymmetricTest()
      .input( clause({ ap(notP(), a) == ap(notP(), xs) }))
      .expected(none())
    )

// not done for variables
TEST_GENERATION(fail_5,
    Generation::AsymmetricTest()
      .input( clause({ xs == ys }))
      .expected(none())
    )

// not done for true or false
TEST_GENERATION(fail_6,
    Generation::AsymmetricTest()
      .input( clause({ troo == ys, ap(f, x) == fols }))
      .expected(none())
    )

// only done to lhs of two bool sides
TEST_GENERATION(success_1,
    Generation::AsymmetricTest()
      .input( clause({ a == b }))
      .expected(exactly(clause({ ap(notP(),a) != b })))
    )

// only done to rhs when lhs is already a not proxy
TEST_GENERATION(success_2,
    Generation::AsymmetricTest()
      .input( clause({ ap(notP(),ap(f,x)) == b }))
      .expected(exactly(clause({ ap(notP(),ap(f,x)) != ap(notP(),b) })))
    )

// only done for the first literal found
TEST_GENERATION(success_3,
    Generation::AsymmetricTest()
      .input( clause({ b == ap(lam(srt, ap(f,db0)),c), a == xs }))
      .expected(exactly(clause({ ap(notP(),b) != ap(lam(srt, ap(f,db0)),c), a == xs })))
    )

TEST_GENERATION(success_4,
    Generation::AsymmetricTest()
      .input( clause({ a != xs, ap(f, x) == fols, b == ap(lam(srt, ap(f,db0)),c), a == xs }))
      .expected(exactly(clause({ a != xs, ap(f, x) == fols, ap(notP(),b) != ap(lam(srt, ap(f,db0)),c), a == xs })))
    )
