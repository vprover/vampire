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
#include "Inferences/FasterCondensation.hpp"

#include "Test/SimplificationTester.hpp"

using namespace Test;

namespace {

#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_SORT(s)                                                                                                \
  DECL_SORT(s2)                                                                                               \
  DECL_FUNC(f, {s}, s)                                                                                        \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_FUNC(h, {s, s}, s)                                                                                     \
  DECL_CONST(a, s)                                                                                            \
  DECL_CONST(b, s)                                                                                            \
  DECL_CONST(c, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (p1, {s, s, s})                                                                                   \
  DECL_PRED (q, {s})                                                                                          \
  DECL_PRED (q1, {s, s})

#define MY_SIMPL_RULE   FasterCondensation
#define MY_SIMPL_TESTER Simplification::SimplificationTester

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
      .expected(clause({ ~p(g(f(x))), q(x), ~p(g(z)), g(x) != x }))
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

TEST_SIMPLIFY(test06,
    Simplification::Success()
      .input(clause({  p(h(x,y)), p(h(a,b)), q(x), q(a) }))
      .expected(clause({ p(h(a,b)), q(a) }))
    )

// condensation does not happen with variables mapped to each other
TEST_SIMPLIFY(test07,
    Simplification::NotApplicable()
      .input(clause({  p(h(x,y)), p(h(y,x)) }))
    )

TEST_SIMPLIFY(test08,
    Simplification::Success()
      .input(clause({  p1(a,y,z), p1(a,b,c), p1(x,y,c) }))
      .expected(clause({ p1(a,b,c) }))
    )

TEST_SIMPLIFY(test09,
    Simplification::NotApplicable()
      .input(clause({  x.sort(s) == y, y.sort(s) == z, x.sort(s) == z }))
    )

TEST_SIMPLIFY(test10,
    Simplification::Success()
      .input(clause({  q1(x,f(x)), q1(x,y) }))
      .expected(clause({ q1(x,f(x)) }))
    )

TEST_SIMPLIFY(test11,
    Simplification::NotApplicable()
      .input(clause({  q1(x,f(x)), ~q1(x,y), p(z), ~p(g(y)) }))
    )

TEST_SIMPLIFY(test12,
    Simplification::NotApplicable()
      .input(clause({  q1(x,y), q1(y,x) }))
    )

TEST_SIMPLIFY(test13,
    Simplification::Success()
      .input(clause({  q1(x,y), q1(y,z), q1(a,x), q1(a,a) }))
      .expected(clause({ q1(a,a) }))
    )

TEST_SIMPLIFY(test14,
    Simplification::NotApplicable()
      .input(clause({  x == a, y.sort(s2) == z }))
    )

}