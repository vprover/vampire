/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/GenerationTester.hpp"

#include "Inferences/BinaryResolution.hpp"

using namespace Test;

/**
 * NECESSARY: We need to tell the tester which syntax sugar to import for creating terms & clauses.
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_VAR(u, 3)                                                                                              \
  DECL_SORT(s)                                                                                                \
  DECL_FUNC(f, {s, s}, s)                                                                                     \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_CONST(b, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})                                                                                          \

REGISTER_GEN_TESTER(Generation::GenerationTester<BinaryResolution>(BinaryResolution()))

// binary resolution with selected literals
TEST_GENERATION(test_01,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(p(x)), f(x,y) == x  }),
        clause({ selected(~p(g(x))), ~q(x) })
      })
      .expected(exactly(clause({ f(g(x),y) == g(x), ~q(x) })))
    )

// no binary resolution with equalities
TEST_GENERATION(test_02,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(g(x) == x), f(x,y) == x  }),
        clause({ selected(g(x) != x), ~q(x) })
      })
      .expected(none())
    )
