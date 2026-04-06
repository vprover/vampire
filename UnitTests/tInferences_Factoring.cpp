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

#include "Inferences/Factoring.hpp"

using namespace Test;

#define MY_GEN_RULE   Factoring
#define MY_GEN_TESTER Generation::GenerationTester

/**
 * NECESSARY: We need to tell the tester which syntax sugar to import for creating terms & clauses.
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_SORT(s)                                                                                                \
  DECL_FUNC(f, {s}, s)                                                                                        \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_CONST(b, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})

// no factoring for unit clauses
TEST_GENERATION(test01,
    Generation::AsymmetricTest()
      .input( clause({ selected(p(f(x))) }))
      .expected(none())
    )

// no factoring for equalities
TEST_GENERATION(test02,
    Generation::AsymmetricTest()
      .input( clause({ selected(f(x) == x), selected(f(f(y)) == f(y)) }))
      .expected(none())
    )

// no factoring for negative literals
TEST_GENERATION(test03,
    Generation::AsymmetricTest()
      .input( clause({ selected(~p(f(x))), selected(~p(y)) }))
      .expected(none())
    )

// no factoring for non-unifiable predicates
TEST_GENERATION(test04,
    Generation::AsymmetricTest()
      .input( clause({ selected(p(f(x))), selected(q(y)) }))
      .expected(none())
    )

// no factoring for non-unifiable functions
TEST_GENERATION(test05,
    Generation::AsymmetricTest()
      .input( clause({ selected(p(f(x))), selected(p(g(y))) }))
      .expected(none())
    )

// no factoring for non-selected literals
TEST_GENERATION(test06,
    Generation::AsymmetricTest()
      .input( clause({ p(f(x)), p(y) }))
      .expected(none())
    )

// factoring between positive literals where one is selected
TEST_GENERATION(test07,
    Generation::AsymmetricTest()
      .input( clause({ selected(p(f(x))), p(y) }))
      .expected(exactly(clause({ p(f(x)) })))
    )

// factoring between only two positive literals
TEST_GENERATION(test08,
    Generation::AsymmetricTest()
      .input( clause({ selected(p(f(x))), p(y), p(f(g(z))) }))
      .expected(exactly(
        clause({ p(f(x)), p(f(g(y))) }),
        clause({ p(f(g(x))), p(y) })
      ))
    )
