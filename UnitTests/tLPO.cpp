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
#include "Kernel/LPO.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Problem.hpp"

inline void compareTwoWays(const Ordering& ord, TermSugar t1, TermSugar t2) {
  ASS_EQ(ord.compare(t1, t2), Ordering::Result::GREATER);
  ASS_EQ(ord.compare(t2, t1), Ordering::Result::LESS);
}

LPO lpo() {
  return LPO(
      DArray<int>::fromIterator(getRangeIterator(0, (int) env.signature->functions())),
      DArray<int>::fromIterator(getRangeIterator(0, (int) env.signature->typeCons())), 
      DArray<int>::fromIterator(getRangeIterator(0, (int) env.signature->predicates())),
      PrecedenceOrdering::testLevels(), false /* reverseLCM */);
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// TEST CASES //////////////////////////////////
//
// How to read the test cases in this file:
//
TEST_FUN(lpo_test01) {
  DECL_DEFAULT_VARS              // <- macro to initialize some syntax sugar for creating terms over a single uninterpreted sort
  DECL_SORT(srt)                 // <- declares a function symbol with arity 1
  DECL_FUNC (f, {srt, srt}, srt) // <- declares a function symbol with arity 2
  DECL_FUNC (g, {srt, srt}, srt) // <- declares a function symbol with arity 2
  DECL_CONST(c, srt)             // <- declares a constant symbol
 
  // !!! The declaration order of function and constant symbols will define their precedence relation !!!
  auto ord = lpo();
  compareTwoWays(ord, g(f(x,y),c), c);
}

TEST_FUN(lpo_test02) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (s, {srt}, srt)
  DECL_FUNC (plus, {srt, srt}, srt)
  DECL_FUNC (mult, {srt, srt}, srt)
  DECL_CONST(zero, srt)

  auto ord = lpo();
  compareTwoWays(ord, plus(zero,x), x);
  compareTwoWays(ord, mult(zero,x), zero);
  compareTwoWays(ord, s(x),         x);
  compareTwoWays(ord, plus(s(x),y), s(plus(x,y)));
  compareTwoWays(ord, mult(s(x),y), plus(mult(x,y),y));
}

TEST_FUN(lpo_test03) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (g, {srt, srt}, srt)
  DECL_FUNC (f, {srt, srt}, srt)

  auto ord = lpo();
  compareTwoWays(ord, f(x,g(y,z)), g(f(x,y),f(x,z)));
  compareTwoWays(ord, f(g(x,y),z), g(f(x,z),f(y,z)));
  compareTwoWays(ord, g(g(x,y),z), g(x,g(y,z)));
}

TEST_FUN(lpo_test04) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (g, {srt}, srt)
  DECL_FUNC (f, {srt, srt}, srt)

  auto ord = lpo();
  compareTwoWays(ord, f(g(x),y), g(f(x,f(x,y))));
  compareTwoWays(ord, f(x,x),    g(g(x)));
}

TEST_FUN(lpo_test05) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (g, {srt, srt}, srt)
  DECL_FUNC (f, {srt, srt}, srt)

  auto ord = lpo();
  ASS_EQ(ord.compare(x, y),                Ordering::Result::INCOMPARABLE);
  ASS_EQ(ord.compare(f(x,y), z),           Ordering::Result::INCOMPARABLE);
  ASS_EQ(ord.compare(g(x,y), f(f(z,z),z)), Ordering::Result::INCOMPARABLE);
}

TEST_FUN(lpo_test06) {
  DECL_DEFAULT_VARS
  NUMBER_SUGAR(Int)
  DECL_FUNC(f, {Int}, Int)
  auto minusR = FuncSugar(RealTraits::minusF());

  auto ord = lpo();

  auto t1 = minus(f(x));
  auto t2 = minusR(toReal(f(x)));
  auto t3 = toReal(minus(f(x)));

  compareTwoWays(ord, t3, t1);
  compareTwoWays(ord, t3, t2);
  compareTwoWays(ord, t1, t2);
}