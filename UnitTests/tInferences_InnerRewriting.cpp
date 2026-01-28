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
#include "Inferences/InnerRewriting.hpp"

#include "Test/SimplificationTester.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

namespace {

#define MY_SIMPL_RULE   InnerRewriting
#define MY_SIMPL_TESTER Simplification::SimplificationTester

/**
 * NECESSARY: We need to tell the tester which syntax sugar to import for creating terms & clauses.
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_VAR(u, 3)                                                                                              \
  DECL_SORT(s)                                                                                                \
  DECL_LEFT_FUNC(left, {s}, s)                                                                                \
  DECL_RIGHT_FUNC(right, {s}, s)                                                                              \
  DECL_FUNC(f, {s, s}, s)                                                                                     \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_CONST(b, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})

// inner rewriting with preordered equation
TEST_SIMPLIFY_WITH_SATURATION(test01,
  Simplification::Success()
    .input(clause({ ~p(f(x,y)), f(x,y) != x, q(y) }))
    .expected(clause({ ~p(x), f(x,y) != x, q(y) }))
  )

// inner rewriting fails with postordered equation
TEST_SIMPLIFY_WITH_SATURATION(test02,
  Simplification::NotApplicable()
    .input(clause({ ~p(f(x,y)), f(x,y) == f(y,x) }))
)

// inner rewriting not performed with positive equations
TEST_SIMPLIFY_WITH_SATURATION(test03,
  Simplification::Success()
    .input(clause({ ~p(f(x,y)), f(x,y) == x }))
    .expected(clause({ ~p(f(x,y)), f(x,y) == x }))
  )

// inner rewriting to tautology
TEST_SIMPLIFY_WITH_SATURATION(test04,
  Simplification::Success()
    .input(clause({ g(f(x,y)) == g(x), f(x,y) != x }))
    .expected(Simplification::Redundant{})
  )

// inner rewriting to tautology after rewriting a non-tautological literal
TEST_SIMPLIFY_WITH_SATURATION(test05,
  Simplification::Success()
    .input(clause({ q(z), p(f(x,y)), g(f(x,y)) == g(x), f(x,y) != x }))
    .expected(Simplification::Redundant{})
  )

}