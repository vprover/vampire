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
#include "Inferences/Injectivity.hpp"

#include "Test/GenerationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_SORT(srt)                                   \
  DECL_LAM                                         \
  DECL_APP                                         \
  DECL_DEFAULT_VARS                                \
  DECL_CONST(f, arrow({srt, srt}, srt))            \
  DECL_CONST(g, arrow(srt, srt))                   \
  DECL_CONST(a, srt)                               \
  DECL_CONST(b, srt)                               \
  NEXT_INTRODUCED_FUN(inv, 0)

#define MY_GEN_RULE   Injectivity
#define MY_GEN_TESTER Generation::GenerationTester

// not done if the var equality is negative
TEST_GENERATION(fail_1,
    Generation::AsymmetricTest()
      .input( clause({ ap(g, x) != ap(g, y), x.sort(srt) != y }))
      .expected(none())
    )

// not done if the other equality is positive
TEST_GENERATION(fail_2,
    Generation::AsymmetricTest()
      .input( clause({ ap(g, x) == ap(g, y), x.sort(srt) == y }))
      .expected(none())
    )

TEST_GENERATION(success_1,
    Generation::AsymmetricTest()
      .input( clause({ x.sort(srt) == y, ap(g, x) != ap(g, y) }))
      .EXPECTED(exactly(clause({ ap(inv(), ap(g, x)) == x })))
    )

// TEST_GENERATION(success_2,
//     Generation::AsymmetricTest()
//       .input( clause({ x == y, ap(f, {x, a}) != ap(f, {y, a}) }))
//       .EXPECTED(exactly(clause({ ap(inv(), ap(f, {x, a})) == x })))
//     )
