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
#include "Inferences/HOL/LeibnizEqualityElimination.hpp"

#include "Test/GenerationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_SORT(srt)                                   \
  DECL_SORT_BOOL                                   \
  DECL_DEFAULT_VARS                                \
  TROO                                             \
  FOLS                                             \
  DECL_NOT_PROXY                                   \
  DECL_EQ_PROXY                                    \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                \
  DECL_CONST(f, arrow(srt,srt))                    \
  DECL_CONST(b, srt)                               \
  DECL_CONST(c, srt)

#define MY_GEN_RULE   LeibnizEqualityElimination
#define MY_GEN_TESTER Generation::GenerationTester

// not done for different vars
TEST_GENERATION(fail_1,
  Generation::AsymmetricTest()
    .input(clause({ ap(x.sort(arrow(srt,Bool)),b) == troo, ap(y.sort(arrow(srt,Bool)), c) == fols }))
    .expected(none())
  )

TEST_GENERATION(success_1,
  Generation::AsymmetricTest()
    .input(clause({ ap(x.sort(arrow(srt,Bool)),b) != fols, ap(x.sort(arrow(srt,Bool)), c) == fols }))
    .expected(exactly(
      clause({ b == c }),
      clause({ b == c })
    ))
  )

TEST_GENERATION(success_2,
  Generation::AsymmetricTest()
    .input(clause({ ap(x.sort(arrow(srt,Bool)),b) == fols, x == lam(srt, troo), ap(x.sort(arrow(srt,Bool)), ap(f, y)) != fols }))
    .expected(exactly(
      clause({ b == ap(f, x), ap(eqP(srt), b) == lam(srt, troo) }),
      clause({ b == ap(f, x), lam(srt, ap(notP, ap(eqP(srt), {db0, ap(f, x)}))) == lam(srt, troo) })
    ))
  )

TEST_GENERATION(success_3,
  Generation::AsymmetricTest()
    .input(clause({ x != lam(srt, troo), ap(x.sort(arrow(srt,Bool)),ap(f,y)) == troo, ap(x.sort(arrow(srt,Bool)), c) == fols }))
    .expected(exactly(
      clause({ ap(f, x) == c, ap(eqP(srt), c) != lam(srt, troo) }),
      clause({ ap(f, x) == c, lam(srt, ap(notP, ap(eqP(srt), {db0, ap(f, x)}))) != lam(srt, troo) })
    ))
  )
