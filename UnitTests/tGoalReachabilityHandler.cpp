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
  DECL_FUNC(h, {s, s, s}, s)

class SymmetricTester {
public:
  SymmetricTester(
    std::initializer_list<Clause*> clauses,
    std::initializer_list<Clause*> goalClauses)
    : clauses(clauses)
  {
    for (const auto& cl : goalClauses) { ALWAYS(expectedGoalClauses.insert(cl)); }
  }

  void run() const {
    Problem prb;
    Options opt;
    opt.resolveAwayAutoValues(prb);
    auto ord = Ordering::create(prb, opt);

    auto indices = Stack<unsigned>::fromIterator(range(0, clauses.size()));
    do {

      DHSet<Clause*> goalClauses;
      GoalReachabilityHandler handler(*ord);

      for (const auto& index : indices) {
        clauses[index]->unmakeGoalClause();
        auto [gcls, kvs] = handler.addClause(clauses[index]);
        // TODO test kvs too
        for (const auto& gc : gcls) {
          ASS_REP(goalClauses.insert(gc), gc->toString() + " removed multiple times");
        }
      }

      for (const auto& cl : iterTraits(goalClauses.iter())) {
        ASS_REP(expectedGoalClauses.contains(cl), cl->toString() + " is not expected to be goal clause");
      }
      for (const auto& cl : iterTraits(expectedGoalClauses.iter())) {
        ASS_REP(goalClauses.contains(cl), cl->toString() + " is expected to be goal clause");
      }

    } while (std::next_permutation(indices.begin(), indices.end()));
  }
private:
  ClauseStack clauses;
  DHSet<Clause*> expectedGoalClauses;
};

TEST_FUN(test01) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  auto c1 = clause({ a != b });
  auto c2 = clause({ f(x,x) == x });
  auto c3 = clause({ f(f(x,y),z) == f(x,f(y,z)) });

  SymmetricTester tester({ c1, c2, c3 }, { c1, c2 });
  tester.run();
}

TEST_FUN(test02) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  auto c1 = clause({ f(a,f(b,a)) != b });
  auto c2 = clause({ f(a,b) == b });

  SymmetricTester tester({ c1, c2 }, { c1, c2 });
  tester.run();
}

TEST_FUN(test03) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  auto c1 = clause({ f(a,f(b,a)) != b });
  auto c2 = clause({ f(f(x,y),z) == f(x,f(y,z)) });
  auto c3 = clause({ f(c,f(c,d)) == f(c,d) });

  // c3 also added due to giving up at the limit of iteration
  SymmetricTester tester({ c1, c2, c3 }, { c1, c2, c3 });
  tester.run();
}

TEST_FUN(test04) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  auto c1 = clause({ f(a,b) != b });
  auto c2 = clause({ f(f(x,y),z) == f(x,y) });
  auto c3 = clause({ f(c,f(c,d)) == f(c,d) });

  // iteration for c3 stops because loop is detected
  SymmetricTester tester({ c1, c2, c3 }, { c1, c2 });
  tester.run();
}

TEST_FUN(test05) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  auto c1 = clause({ a != b });
  auto c2 = clause({ h(x,x,y) == y });
  auto c3 = clause({ h(f(c,x),d,b) == a });
  auto c4 = clause({ f(x,c) == d });

  // iteration for c3 stops because loop is detected
  SymmetricTester tester({ c1, c2, c3, c4 }, { c1, c2 });
  tester.run();
}