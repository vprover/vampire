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
#include "Inferences/Condensation.hpp"

#include "Test/SimplificationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_SORT(s)                                                                                                \
  DECL_FUNC(f, {s}, s)                                                                                        \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_CONST(b, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})

REGISTER_SIMPL_TESTER(Simplification::RuleSimplificationTester<Condensation>)

// nothing happens with one literal
TEST_SIMPLIFY(test01,
    Simplification::NotApplicable()
      .input(clause({  f(x) == a }))
    )

// condensation happens with two literals
TEST_SIMPLIFY(test02,
    Simplification::Success()
      .input(clause({  f(g(x)) == a, f(y) == a }))
      .expected(clause({ f(g(x)) == a }))
    )

// condensation happens between first two literals found
TEST_SIMPLIFY(test03,
    Simplification::Success()
      .input(clause({  ~p(g(f(x))), q(x), ~p(y), ~p(g(z)), g(x) != x }))
      .expected(clause({ ~p(g(f(x))), q(x), ~p(g(y)), g(x) != x }))
    )

// condensation does not happen due to some literal that needs to be instantiated
TEST_SIMPLIFY(test04,
    Simplification::NotApplicable()
      .input(clause({  ~p(f(x)), ~p(y), q(y) }))
    )

// condensation happens but not with first two literals due to some literal that would need to be instantiated
TEST_SIMPLIFY(test05,
    Simplification::Success()
      .input(clause({  ~p(g(f(x))), ~p(g(y)), ~p(z), q(y) }))
      .expected(clause({ ~p(g(f(x))), ~p(g(y)), q(y) }))
    )
