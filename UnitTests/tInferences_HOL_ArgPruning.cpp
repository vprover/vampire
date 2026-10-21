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
  DECL_CONST(f, arrow({s, s}, s))                  \
  DECL_CONST(a, s)                                 \
  DECL_CONST(b, s)                                 \
  DECL_CONST(c, s)                                 \
  DECL_CONST(d, s)                                 \

#define MY_SIMPL_RULE   ArgPruning
#define MY_SIMPL_TESTER Simplification::SimplificationTester

// occurrence with not enough arguments
TEST_SIMPLIFY(fail01,
    Simplification::NotApplicable()
      .input(clause({ ap(ap(x.sort(arrow({s, s}, s)), b), b) == a, x != f }))
    )

// same argument in all occurrences, but wrong position
TEST_SIMPLIFY(fail02,
    Simplification::NotApplicable()
      .input(clause({ ap(ap(x.sort(arrow({s, s}, s)), c), a) == a, ap(x.sort(arrow({s, s}, s)), a) != ap(f, c) }))
    )

// repeated arguments
TEST_SIMPLIFY(success01,
    Simplification::Success()
      .input(clause({ ap(ap(x.sort(arrow({s, s}, s)), b), b) == a, ap(ap(x.sort(arrow({s, s}, s)), a), a) != c }))
      .expected(clause({ ap(x.sort(arrow(s, s)), b) == a, ap(x.sort(arrow(s, s)), a) != c }))
    )

// same argument in all occurrences
TEST_SIMPLIFY(success02,
    Simplification::Success()
      .input(clause({ ap(ap(x.sort(arrow({s, s}, s)), a), c) == a, ap(ap(x.sort(arrow({s, s}, s)), a), b) != c }))
      .expected(clause({ ap(x.sort(arrow(s, s)), c) == a, ap(x.sort(arrow(s, s)), b) != c }))
    )

// same argument in all occurrences, one partially applied
TEST_SIMPLIFY(success03,
    Simplification::Success()
      .input(clause({ ap(ap(x.sort(arrow({s, s}, s)), a), c) == a, ap(x.sort(arrow({s, s}, s)), a) != ap(f, c) }))
      .expected(clause({ ap(x.sort(arrow(s, s)), c) == a, x != ap(f, c) }))
    )

// only one occurrence of the variables
TEST_SIMPLIFY(success04,
    Simplification::Success()
      .input(clause({ ap(ap(x.sort(arrow({s, s}, s)), a), b) == a, ap(ap(y.sort(arrow({s, s}, s)), c), d) != c }))
      .expected(clause({ x == a, y != c }))
    )

// one with variables in terms: x a (f a c) b != x z (f z c) b
TEST_SIMPLIFY(success05,
    Simplification::Success()
      .input(clause({ ap(ap(x.sort(arrow({s, s, s}, s)), a), {ap(f, {a, c}), b}) != ap(ap(x.sort(arrow({s, s, s}, s)), z), {ap(f, {z, c}), b}) }))
      .expected(clause({ ap(x.sort(arrow(s, s)), a) != ap(x.sort(arrow(s, s)), z) }))
    )

// applied variables as subterms
TEST_SIMPLIFY(success06,
    Simplification::Success()
      .input(clause({ ap(f, { ap(x.sort(arrow(s, s)), a), ap(x.sort(arrow(s, s)), a) }) != c }))
      .expected(clause({ ap(f, {x, x}) != c }))
    )