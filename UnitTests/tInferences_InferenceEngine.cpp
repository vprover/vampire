/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Kernel/Clause.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Inferences/InferenceEngine.hpp"

#include "Test/SimplificationTester.hpp"

using namespace Test;

#define MY_SIMPL_TESTER Simplification::SimplificationTester
#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_SORT(s)                                                                                                \
  DECL_FUNC(f, {s, s}, s)                                                                                     \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_CONST(b, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})                                                                                          \

namespace {

#define MY_SIMPL_RULE DuplicateLiteralRemovalISE

TEST_SIMPLIFY(dlr_test01,
    Simplification::NotApplicable()
      .input(clause({ p(a) }))
    )

TEST_SIMPLIFY(dlr_test02,
    Simplification::Success()
      .input(clause({ p(a), p(a) }))
      .expected(clause({ p(a) }))
    )

TEST_SIMPLIFY(dlr_test03,
    Simplification::NotApplicable()
      .input(clause({ p(a), q(b) }))
    )

TEST_SIMPLIFY(dlr_test04,
    Simplification::NotApplicable()
      .input(clause({ p(x), p(y) }))
    )

TEST_SIMPLIFY(dlr_test05,
    Simplification::Success()
      .input(clause({ p(a), ~p(x), q(f(a,y)), q(b), q(f(a,y)), p(a), ~p(x), p(a) }))
      .expected(clause({ p(a), ~p(x), q(f(a,y)), q(b) }))
    )

TEST_SIMPLIFY(dlr_test06,
    Simplification::Success()
      .input(clause({ p(a), ~p(a), ~p(a), p(a), q(b) }))
      .expected(clause({ p(a), ~p(a), q(b) }))
    )

TEST_SIMPLIFY(dlr_test07,
    Simplification::NotApplicable()
      .input(clause({ p(a), f(x,y) == x, q(b) }))
    )

TEST_SIMPLIFY(dlr_test08,
    Simplification::Success()
      .input(clause({ f(x,y) == x, f(x,y) == x, q(b) }))
      .expected((clause({ f(x,y) == x, q(b) })))
    )
}

namespace {

#undef MY_SIMPL_RULE
#define MY_SIMPL_RULE TrivialInequalitiesRemovalISE

TEST_SIMPLIFY(tir_test01,
    Simplification::NotApplicable()
      .input(clause({ a == b }))
    )

TEST_SIMPLIFY(tir_test02,
    Simplification::NotApplicable()
      .input(clause({ a != b }))
    )

TEST_SIMPLIFY(tir_test03,
    Simplification::NotApplicable()
      .input(clause({ a == a }))
    )

TEST_SIMPLIFY(tir_test04,
    Simplification::Success()
      .input(clause({ a != a }))
      .expected(clause({ }))
    )

TEST_SIMPLIFY(tir_test05,
    Simplification::Success()
      .input(clause({ p(a), a != a, f(x,y) != g(y), f(x,y) != f(x,y), ~q(x), a != a, g(y) == g(y) }))
      .expected(clause({ p(a), f(x,y) != g(y), ~q(x), g(y) == g(y) }))
    )
}
