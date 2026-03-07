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

#define MY_SYNTAX_SUGAR                            \
  DECL_DEFAULT_VARS                                \
  DECL_SORT(srt)                                   \
  DECL_VAR_SORTED(xs, 0, arrow({ srt, srt }, srt)) \
  DECL_PRED(p, { arrow({srt, srt}, srt) })         \
  DECL_FUNC(f, {srt, srt}, srt)                    \
  DECL_CONST(g, arrow({srt, srt}, srt))            \
  DECL_CONST(g1, arrow({srt, srt}, srt))           \
  DECL_CONST(h, arrow({srt, srt, srt}, srt))       \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                \
  DECL_DE_BRUIJN_INDEX(db1, 1, srt)                \
  DECL_CONST(a, {srt})                             \
  DECL_CONST(b, {srt})                             \
  NEXT_INTRODUCED_PRED(p_hol,0)                    \
  NEXT_INTRODUCED_PRED(q_hol,1)

#define PREAMBLE_HANDLER           \
  env.setHigherOrder(true);        \
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR); \
  Options opt;                     \
  HOLUnifierHandler handler(opt);

void checkEqual(Clause* actual, Clause* expected) {
  if (!TestUtils::eqModAC(actual, expected)) {
    std::cout  << std::endl;
    std::cout << "[   actual ]: " << pretty(actual) << std::endl;
    std::cout << "[ expected ]: " << pretty(expected) << std::endl;
    ASSERTION_VIOLATION;
  }
}

TEST_FUN(no_constraints_1) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ f(a,a) == a });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, c1);
}

TEST_FUN(no_constraints_2) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ f(x,y) != a, x == a });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, c1);
}

TEST_FUN(constraints_1) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ ap(g,y) != lam(srt, db0), y == a });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, clause({ ~p_hol(y), y == a }));
}

TEST_FUN(constraints_2) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ ap(g,y) != lam(srt, db0), y == a, ap(ap(h,y),z) != lam(srt, db0), f(y,z) != b });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, clause({ ~p_hol(y), y == a, ~q_hol(y,z), f(y,z) != b }));
}

TEST_FUN(constraints_3) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ y == a, ap(ap(h,y),z) != lam(srt, db0), f(y,z) != b });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, clause({ y == a, ~p_hol(y,z), f(y,z) != b }));
}

TEST_FUN(constraints_different) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ ap(g,y) != lam(srt, db0), y == a });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, clause({ ~p_hol(y), y == a }));

  auto d1 = clause({ ap(ap(h,z),b) != lam(srt, db0), f(y,z) != b });
  auto d2 = handler.handleClause(d1);

  checkEqual(d2, clause({ ~q_hol(z), f(y,z) != b }));
}

TEST_FUN(constraints_same) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ ap(g,y) != lam(srt, db0), y == a });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, clause({ ~p_hol(y), y == a }));

  auto d1 = clause({ ap(g,z) != lam(srt, db0), f(y,z) != b });
  auto d2 = handler.handleClause(d1);

  checkEqual(d2, clause({ ~p_hol(z), f(y,z) != b }));
}

void testUnifier(Literal* constraint, Literal* def, unsigned nextVar, Stack<LiteralStack> expected)
{
  HOLUnifier unifier(constraint, def, nextVar);

  for (unsigned i = 0; i < expected.size(); i++) {
    LiteralStack solution;
    auto finished = unifier.iterate(solution);
    if ((i+1 == expected.size()) != finished) {
      std::cout << "unifier should " << (finished ? "not" : "") << " finish in iteration " << i << std::endl;
      ASSERTION_VIOLATION;
    }
    if (expected[i] != solution) {
      std::cout << "unifier should result in " << pretty(expected[i]) << " not in " << pretty(solution) << " in iteration " << i << std::endl;
      ASSERTION_VIOLATION;
    }
  }
}

#define TEST_UNIFIER(name, ...)      \
  TEST_FUN(name) {                   \
    env.setHigherOrder(true);        \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR); \
    testUnifier(__VA_ARGS__);        \
  }

TEST_UNIFIER(constraints_iteration_1,
  ap(ap(xs, a), b) == ap(ap(g, b), a), p(xs), 1,
  Stack<LiteralStack>{
    LiteralStack(),
    LiteralStack(),
    LiteralStack(),
    LiteralStack(),
    LiteralStack{ p(lam(srt, lam(srt, ap(ap(g, db0), db1)))) },
    LiteralStack{ p(lam(srt, lam(srt, ap(ap(g, db0), a)))) },
    LiteralStack(),
    LiteralStack{ p(lam(srt, lam(srt, ap(ap(g, b), db1)))) },
    LiteralStack{ p(lam(srt, lam(srt, ap(ap(g, b), a)))) },
    LiteralStack(),
    LiteralStack{ p(lam(srt, lam(srt, ap(ap(g, db0), db1)))) },
    LiteralStack{ p(lam(srt, lam(srt, ap(ap(g, b), db1)))) },
    LiteralStack(),
    LiteralStack{ p(lam(srt, lam(srt, ap(ap(g, db0), a)))) },
    LiteralStack{ p(lam(srt, lam(srt, ap(ap(g, b), a)))) },
  }
)

TEST_UNIFIER(constraints_iteration_2,
  g() == g(), p(xs), 1,
  Stack<LiteralStack>{
    LiteralStack{ p(xs) },
  }
)

TEST_UNIFIER(constraints_iteration_3,
  g() == g1(), p(xs), 1,
  Stack<LiteralStack>{
    LiteralStack(),
  }
)

TEST_UNIFIER(constraints_iteration_4,
  g() == lam(srt, ap(g, db0)), p(xs), 1,
  Stack<LiteralStack>{
    LiteralStack{ p(xs) },
  }
)

// TODO handle decomposition
// TEST_UNIFIER(constraints_iteration_5,
//   lam(srt, ap(g, db0)) == lam(srt, lam(srt, ap(ap(g, db0), db1))), p(xs), 1,
//   Stack<LiteralStack>{
//     LiteralStack(),
//   }
// )
