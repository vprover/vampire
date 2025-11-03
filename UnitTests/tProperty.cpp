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

#include "Shell/Property.hpp"

using namespace Shell;

/**
 * NECESSARY: We need to tell the tester which syntax sugar to import for creating terms & clauses.
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                    \
  DECL_DEFAULT_VARS                                                                        \
  DECL_SORT(s)                                                                             \
  DECL_FUNC(f, {s}, s)                                                                     \
  DECL_CONST(c, s)                                                                         \
  DECL_PRED(p, {s})                                                                        \

TEST_FUN(test01) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  auto units = UnitList::empty();
  UnitList::push(clause({ f(c) == c, ~p(x) }), units);
  UnitList::push(formula(f(c) != c), units);

  auto prop = Property::scan(units);
  ASS_EQ(prop->category(), Property::NEQ);
}
