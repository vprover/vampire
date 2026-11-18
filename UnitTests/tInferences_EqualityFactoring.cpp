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

#include "Inferences/EqualityFactoring.hpp"

using namespace Test;

namespace {

#define MY_GEN_RULE   EqualityFactoring
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
  DECL_PRED (p, {s})

// inferences is performed
TEST_GENERATION(test01,
  Generation::AsymmetricTest()
    .input( clause({  selected(f(f(x)) == x), f(y) == y, g(x) == x, p(y) }))
    .expected({ clause({ f(f(x)) == f(x), f(x) != x, g(x) == x, p(f(x)) }) })
  )

// not performed because on of the literal is not selected
TEST_GENERATION(test02,
  Generation::AsymmetricTest()
    .input( clause({  f(f(x)) == x, f(y) == y, selected(g(x) == x), p(y) }))
    .expected(none())
  )

#undef MY_SYNTAX_SUGAR
#define MY_SYNTAX_SUGAR                               \
  DECL_SORT(s)                                        \
  DECL_DEFAULT_VARS                                   \
  DECL_CONST(f, arrow(s, s))                          \
  DECL_DE_BRUIJN_INDEX(db0, 0, s)                     \
  DECL_CONST(a, s)                                    \
  DECL_CONST(b, s)

// with higher-order unification
TEST_GENERATION(test_hol01,
    Generation::AsymmetricTest()
      .input(clause({ selected(ap(x.sort(arrow(s, s)), ap(f, a)) == a), ap(f, a) == b, x != f }))
      .expected( exactly(
        clause({ b == ap(f, a), ap(f, a) != a, lam(s, b) != f() }),
        clause({ ap(f, a) == b, b != a, lam(s, db0) != f() }),
        clause({ ap(f, a) == b, b != a, lam(s, ap(f, ap(lam(s, a), db0))) != f() })
      ))
    )

}