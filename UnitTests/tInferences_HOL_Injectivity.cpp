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

// not done if var equality has same args
TEST_GENERATION(fail_3,
    Generation::AsymmetricTest()
      .input( clause({ x.sort(srt) == x, ap(g, x) != ap(g, y) }))
      .expected(none())
    )

// not done if var equality has proper terms
TEST_GENERATION(fail_4,
    Generation::AsymmetricTest()
      .input( clause({ a == x, ap(g, x) != ap(g, y) }))
      .expected(none())
    )

// not done if other equality contains proper term arguments
TEST_GENERATION(fail_5,
    Generation::AsymmetricTest()
      .input( clause({ x.sort(srt) == y, ap(g, a) != ap(g, y) }))
      .expected(none())
    )

// not done if other equality does not contain differring args
TEST_GENERATION(fail_6,
    Generation::AsymmetricTest()
      .input( clause({ x.sort(srt) == y, ap(g, y) != ap(g, y) }))
      .expected(none())
    )

// not done if var equality is missing
TEST_GENERATION(fail_7,
    Generation::AsymmetricTest()
      .input( clause({ ap(g, x) != ap(g, y) }))
      .expected(none())
    )

// not done if other equality is missing
TEST_GENERATION(fail_8,
    Generation::AsymmetricTest()
      .input( clause({ x.sort(srt) == y }))
      .expected(none())
    )

// not done if other equality contains non-variable arguments
TEST_GENERATION(fail_9,
    Generation::AsymmetricTest()
      .input( clause({ x.sort(srt) == y, ap(f, {x, a}) != ap(f, {y, a}) }))
      .expected(none())
    )

// not done if other equality contains arguments in wrong constellation
TEST_GENERATION(fail_10,
    Generation::AsymmetricTest()
      .input( clause({ x.sort(srt) == y, ap(f, {x, y}) != ap(f, {x, z}) }))
      .expected(none())
    )

TEST_GENERATION(success_1,
    Generation::AsymmetricTest()
      .input( clause({ x.sort(srt) == y, ap(g, x) != ap(g, y) }))
      .EXPECTED(exactly(clause({ ap(inv(), ap(g, x)) == x })))
    )

TEST_GENERATION(success_2,
    Generation::AsymmetricTest()
      .input( clause({ x.sort(srt) == y, ap(f, {x, z}) != ap(f, {y, z}) }))
      .EXPECTED(exactly(clause({ ap(inv(), {z, ap(f, {x, z})}) == x })))
    )

TEST_GENERATION(success_3,
    Generation::AsymmetricTest()
      .input( clause({ y.sort(srt) == z, ap(f, {x, z}) != ap(f, {x, y}) }))
      .EXPECTED(exactly(clause({ ap(inv(), {z, ap(f, {x, z})}) == x })))
    )
