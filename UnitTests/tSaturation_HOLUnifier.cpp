/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Debug/Assertion.hpp"
#include "Test/HOLUtils.hpp"
#include "Saturation/HOLUnifier.hpp"
#include "Test/SyntaxSugar.hpp"

using namespace Saturation;
using namespace Test::HOL;

#define MY_SYNTAX_SUGAR                         \
  DECL_DEFAULT_VARS                             \
  DECL_SORT(srt)                                \
  DECL_FUNC(g2, {srt, srt}, srt)                \
  DECL_CONST(h2, arrow({srt, srt}, srt))        \
  DECL_DE_BRUIJN_INDEX(dX, 0, srt)              \
  DECL_CONST(a, {srt})

HOL_TEST_FUN(no_constraints_1) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  HOLUnifier unifier;

  auto c1 = clause({ g2(a,a) == a });
  auto c2 = unifier.handleClause(c1);
  ASS_EQ(c1,c2);
}

HOL_TEST_FUN(no_constraints_2) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  HOLUnifier unifier;

  auto c1 = clause({ g2(x,y) != a, x == a });
  auto c2 = unifier.handleClause(c1);
  ASS_EQ(c1,c2);
}

HOL_TEST_FUN(constraints_1) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  HOLUnifier unifier;

  auto c1 = clause({ ap(h2,y) != lam(srt, dX), y == a });
  auto c2 = unifier.handleClause(c1);
  if (c1 != c2) {
    std::cout << c1->toString() << std::endl;
    std::cout << c2->toString() << std::endl;
    ASSERTION_VIOLATION;
  }
}
