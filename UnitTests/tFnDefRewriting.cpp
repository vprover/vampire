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
#include "Test/TestUtils.hpp"
#include "Test/GenerationTester.hpp"

#include "Inferences/FnDefRewriting.hpp"

using namespace Test;

REGISTER_GEN_TESTER(FnDefRewriting)

/**
 * NECESSARY: We neet to tell the tester which syntax sugar to import for creating terms & clauses. 
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                    \
  DECL_DEFAULT_VARS                                                                        \
  DECL_SORT(s)                                                                             \
  DECL_CONST(b, s)                                                                         \
  DECL_FUNC(r, {s}, s)                                                                     \
  DECL_TERM_ALGEBRA(s, {b, r})                                                             \
  DECL_FUNC(f, {s, s}, s)                                                                  \
  DECL_FUNC(g, {s}, s)                                                                     \
  DECL_PRED(p, {s})                                                                        \
  DECL_FUNC_DEFS({ { clause({ f(b, y) == y }),                               0, false },   \
                   { clause({ f(x,r(y)) == f(r(x), y), x != b() }),          0, true  },   \
                   { clause({ x == r(b()), f(r(x), y) == f(x,y) }),          1, false },   \
                   { clause({ g(b()) == f(b(), b()) }),                      0, false },   \
                   { clause({ p(x), x != b(), g(r(r(x))) == f(r(x),g(x)) }), 2, false } } )

TEST_GENERATION(test_01,
    Generation::TestCase()
      .input( clause({  b != f(b, y), p(x) }))
      .expected(exactly(
              clause({  b != y,       p(x) })
      ))
    )

TEST_GENERATION(test_02,
    Generation::TestCase()
      .input( clause({  g(b)   == g(r(x)), p(x) }))
      .expected(exactly(
              clause({  f(b,b) == g(r(x)), p(x) })
      ))
    )

// no rewrites (matching is used instead of unification)
TEST_GENERATION(test_03,
    Generation::TestCase()
      .input( clause({  g(r(x)) == f(x, r(x)) }))
    )

// multiple rewritten positions in a literal and multiple rewrite rules
TEST_GENERATION(test_04,
    Generation::TestCase()
      .input( clause({  f(r(b),f(b, y)) == f(y, r(y)) }))
      .expected({
              clause({  f(r(b),y)       == f(y, r(y)) }),
              clause({  f(b,f(b, y))    == f(y, r(y)), b == r(b)}),
              clause({  f(b,r(f(b, y))) == f(y, r(y)), b != b})
      })
    )

// each literal is rewritten in a clause
TEST_GENERATION(test_05,
    Generation::TestCase()
      .input( clause({  g(r(r(r(b))))      != b, g(b)   == b }))
      .expected({
              clause({  f(r(r(b)),g(r(b))) != b, g(b)   == b, p(r(b)), r(b) != b() }),
              clause({  g(r(r(r(b))))      != b, f(b,b) != b })
      })
    )

// equational tautologies are discarded
TEST_GENERATION(test_06,
    Generation::TestCase()
      .input( clause({  f(b,b) == b  }))
    )
