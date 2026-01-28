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
#include "Test/GenerationTester.hpp"

#include "Inferences/URResolution.hpp"

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

#define MY_GEN_RULE   URResolution</*synthesis=*/false>
#define MY_GEN_TESTER Generation::GenerationTester

// simple resolution
TEST_GENERATION(test01,
    Generation::SymmetricTest()
      .inputs({
        clause({ p(x), f(x,y) == x }),
        clause({ ~p(g(x)) })
      })
      .options({ { "unit_resulting_resolution", "full" } })
      .expected(exactly(clause({ f(g(x),y) == g(x) })))
    )

// no resolution due to result not being unit
TEST_GENERATION(test02,
    Generation::SymmetricTest()
      .inputs({
        clause({ p(x), f(x,y) == x }),
        clause({ ~p(g(x)), ~q(x) })
      })
      .options({ { "unit_resulting_resolution", "full" } })
      .expected(none())
    )

// resolution with multiple clauses
TEST_GENERATION(test03,
    Generation::SymmetricTest()
      .inputs({
        clause({ f(g(a),b) != g(a) }),
        clause({ p(x) }),
        clause({ ~p(g(x)), ~q(x), f(x,y) == x })
      })
      .options({ { "unit_resulting_resolution", "full" } })
      .expected(exactly(clause({ ~q(g(a)) })))
    )

// resolution with multiple clauses resulting in empty clause
TEST_GENERATION(test04,
    Generation::SymmetricTest()
      .inputs({
        clause({ q(g(y)) }),
        clause({ f(g(a),b) != g(a) }),
        clause({ p(x) }),
        clause({ ~p(g(x)), ~q(x), f(x,y) == x })
      })
      .options({ { "unit_resulting_resolution", "ec_only" } })
      .expected(exactly(clause({ })))
    )
