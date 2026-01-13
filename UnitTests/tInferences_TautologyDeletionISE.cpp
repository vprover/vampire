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
#include "Inferences/TautologyDeletionISE.hpp"

#include "Test/SimplificationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_SORT(s)                                                                                                \
  DECL_FUNC(f, {s, s}, s)                                                                                     \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_CONST(b, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})                                                                                          \

REGISTER_SIMPL_TESTER(Simplification::RuleSimplificationTester<TautologyDeletionISE>)

TEST_SIMPLIFY(test01,
    Simplification::Success()
      .input(clause({ f(x,y) == g(x) }))
      .expected(clause({ f(x,y) == g(x) }))
    )

TEST_SIMPLIFY(test02,
    Simplification::Success()
      .input(clause({ p(x) }))
      .expected(clause({ p(x) }))
    )

TEST_SIMPLIFY(test03,
    Simplification::Success()
      .input(clause({ f(x,y) == f(x,y) }))
      .expected(Simplification::Redundant{})
    )

TEST_SIMPLIFY(test04,
    Simplification::Success()
      .input(clause({ p(x), ~p(y) }))
      .expected(clause({ p(x), ~p(y) }))
    )

TEST_SIMPLIFY(test05,
    Simplification::Success()
      .input(clause({ p(x), ~p(x) }))
      .expected(Simplification::Redundant{})
    )
