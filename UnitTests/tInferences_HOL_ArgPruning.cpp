/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Test/SimplificationTester.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Inferences/HOL/ArgPruning.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_SORT(s)                                     \
  DECL_DEFAULT_VARS                                \
  DECL_CONST(a, s)                                 \
  DECL_CONST(b, s)                                 \
  DECL_CONST(c, s)                                 \
  DECL_CONST(d, s)                                 \

#define MY_SIMPL_RULE   ArgPruning
#define MY_SIMPL_TESTER Simplification::SimplificationTester

// TEST_SIMPLIFY(fail01,
//     Simplification::NotApplicable()
//       .input(clause({ ap(x, {b, b}) == a, ap(x, {a, a}) != c }))
//     )

TEST_SIMPLIFY(success01,
    Simplification::Success()
      .input(clause({ ap(ap(x.sort(arrow({s, s}, s)), b), b) == a, ap(ap(x.sort(arrow({s, s}, s)), a), a) != c }))
      .expected(clause({ ap(x.sort(arrow(s, s)), b) == a, ap(x.sort(arrow(s, s)), a) != c }))
    )

TEST_SIMPLIFY(success02,
    Simplification::Success()
      .input(clause({ ap(ap(x.sort(arrow({s, s}, s)), a), c) == a, ap(ap(x.sort(arrow({s, s}, s)), a), b) != c }))
      .expected(clause({ ap(x.sort(arrow(s, s)), c) == a, ap(x.sort(arrow(s, s)), a) != c }))
    )

TEST_SIMPLIFY(success03,
    Simplification::Success()
      .input(clause({ ap(ap(x.sort(arrow({s, s}, s)), a), b) == a, ap(ap(y.sort(arrow({s, s}, s)), c), d) != c }))
      .expected(clause({ x == a, y != c }))
    )
