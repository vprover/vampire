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

#include "Shell/GoalReachabilityHandler.hpp"

#define MY_SYNTAX_SUGAR                                                                    \
  DECL_DEFAULT_VARS                                                                        \
  DECL_SORT(s)                                                                             \
  DECL_CONST(a, s)                                                                         \
  DECL_CONST(b, s)                                                                         \
  DECL_CONST(c, s)                                                                         \
  DECL_CONST(d, s)                                                                         \
  DECL_FUNC(f, {s, s}, s)                                                                  \
  DECL_FUNC(g, {s}, s)                                                                     \
  DECL_FUNC(h, {s, s}, s)

TEST_FUN(test01) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  Problem prb;
  Options opt;
  opt.resolveAwayAutoValues(prb);
  auto ord = Ordering::create(prb, opt);

  GoalReachabilityHandler handler(*ord, opt);

  auto c1 = clause({ a != b });
  ASS(handler.addClause(c1));

  auto c2 = clause({ f(x,x) == x });
  ASS(handler.addClause(c2));

  auto c3 = clause({ f(f(x,y),z) == f(x,f(y,z)) });
  ASS(!handler.addClause(c3));
}

TEST_FUN(test02) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  Problem prb;
  Options opt;
  opt.resolveAwayAutoValues(prb);
  auto ord = Ordering::create(prb, opt);

  GoalReachabilityHandler handler(*ord, opt);

  auto c1 = clause({ f(a,f(b,a)) != b });
  ASS(handler.addClause(c1));

  auto c2 = clause({ f(a,b) == b });
  ASS(handler.addClause(c2));
}

TEST_FUN(test03) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  Problem prb;
  Options opt;
  opt.resolveAwayAutoValues(prb);
  auto ord = Ordering::create(prb, opt);

  GoalReachabilityHandler handler(*ord, opt);

  auto c1 = clause({ f(a,f(b,a)) != b });
  ASS(handler.addClause(c1));

  auto c2 = clause({ f(f(x,y),z) == f(x,f(y,z)) });
  ASS(handler.addClause(c2));

  // added due to giving up at the limit of iteration
  auto c3 = clause({ f(c,f(c,d)) == f(c,d) });
  ASS(handler.addClause(c3));
}

TEST_FUN(test04) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  Problem prb;
  Options opt;
  opt.resolveAwayAutoValues(prb);
  auto ord = Ordering::create(prb, opt);

  GoalReachabilityHandler handler(*ord, opt);

  auto c1 = clause({ f(a,b) != b });
  ASS(handler.addClause(c1));

  auto c2 = clause({ f(f(x,y),z) == f(x,y) });
  ASS(handler.addClause(c2));

  // iteration stops because loop is detected
  auto c3 = clause({ f(c,f(c,d)) == f(c,d) });
  ASS(!handler.addClause(c3));
}
