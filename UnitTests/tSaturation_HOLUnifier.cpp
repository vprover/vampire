/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Saturation/HOLUnifier.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/TestUtils.hpp"

using namespace Saturation;
using namespace Test;

#define MY_SYNTAX_SUGAR                         \
  DECL_DEFAULT_VARS                             \
  DECL_SORT(srt)                                \
  DECL_FUNC(f, {srt, srt}, srt)                 \
  DECL_CONST(g, arrow({srt, srt}, srt))         \
  DECL_CONST(h, arrow({srt, srt, srt}, srt))    \
  DECL_DE_BRUIJN_INDEX(dX, 0, srt)              \
  DECL_CONST(a, {srt})                          \
  DECL_CONST(b, {srt})                          \
  NEXT_INTRODUCED_PRED(p_hol,0)                 \
  NEXT_INTRODUCED_PRED(q_hol,1)

#define PREAMBLE                   \
  env.setHigherOrder(true);        \
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR); \
  HOLUnifier unifier;

void checkEqual(Clause* actual, Clause* expected) {
  if (!TestUtils::eqModAC(actual, expected)) {
    std::cout  << std::endl;
    std::cout << "[   actual ]: " << pretty(actual) << std::endl;
    std::cout << "[ expected ]: " << pretty(expected) << std::endl;
    ASSERTION_VIOLATION;
  }
}

TEST_FUN(no_constraints_1) {
  PREAMBLE;
  auto c1 = clause({ f(a,a) == a });
  auto c2 = unifier.handleClause(c1);

  checkEqual(c2, c1);
}

TEST_FUN(no_constraints_2) {
  PREAMBLE;
  auto c1 = clause({ f(x,y) != a, x == a });
  auto c2 = unifier.handleClause(c1);

  checkEqual(c2, c1);
}

TEST_FUN(constraints_1) {
  PREAMBLE;
  auto c1 = clause({ ap(g,y) != lam(srt, dX), y == a });
  auto c2 = unifier.handleClause(c1);

  checkEqual(c2, clause({ ~p_hol(y), y == a }));
}

TEST_FUN(constraints_different) {
  PREAMBLE;
  auto c1 = clause({ ap(g,y) != lam(srt, dX), y == a });
  auto c2 = unifier.handleClause(c1);

  checkEqual(c2, clause({ ~p_hol(y), y == a }));

  auto d1 = clause({ ap(ap(h,z),b) != lam(srt, dX), f(y,z) != b });
  auto d2 = unifier.handleClause(d1);

  checkEqual(d2, clause({ ~q_hol(z), f(y,z) != b }));
}

TEST_FUN(constraints_same) {
  PREAMBLE;
  auto c1 = clause({ ap(g,y) != lam(srt, dX), y == a });
  auto c2 = unifier.handleClause(c1);

  checkEqual(c2, clause({ ~p_hol(y), y == a }));

  auto d1 = clause({ ap(g,z) != lam(srt, dX), f(y,z) != b });
  auto d2 = unifier.handleClause(d1);

  checkEqual(d2, clause({ ~p_hol(z), f(y,z) != b }));
}
