/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/TermIterators.hpp"
#include "Saturation/HOLUnifier.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/TestUtils.hpp"

using namespace Saturation;
using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_APP                                         \
  DECL_LAM                                         \
  DECL_SORT(srt)                                   \
  TROO                                             \
  DECL_VAR_SORTED(x, 0, srt)                       \
  DECL_VAR_SORTED(y, 1, srt)                       \
  DECL_VAR_SORTED(z, 2, srt)                       \
  DECL_VAR_SORTED(xs, 3, arrow({ srt, srt }, srt)) \
  DECL_VAR_SORTED(ys, 4, arrow(srt, srt))          \
  DECL_VAR_SORTED(zs, 5, arrow(srt, srt))          \
  DECL_PRED(p, { arrow({srt, srt}, srt) })         \
  DECL_PRED(q, { srt, srt })                       \
  DECL_CONST(f, arrow(srt, srt))                   \
  DECL_CONST(g, arrow({srt, srt}, srt))            \
  DECL_CONST(g1, arrow({srt, srt}, srt))           \
  DECL_CONST(h, arrow({srt, srt, srt}, srt))       \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                \
  DECL_DE_BRUIJN_INDEX(db1, 1, srt)                \
  DECL_CONST(a, srt)                               \
  DECL_CONST(b, srt)                               \
  DECL_CONST(c, srt)                               \
  NEXT_INTRODUCED_FUN(f_hol,0)                     \
  NEXT_INTRODUCED_FUN(g_hol,1)

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
  auto c1 = clause({ ap(f,a) == a });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, c1);
}

TEST_FUN(no_constraints_2) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ ap(f,x) != a, x == a });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, c1);
}

TEST_FUN(no_constraints_3) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ ap(ap(g, y), x) != ap(ap(g, a), b) });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, c1);
}

TEST_FUN(constraints_1) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ ap(g,y) != lam(srt, db0), y == a });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, clause({ ap(f_hol(),y) != troo, y == a }));
}

TEST_FUN(constraints_2) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ ap(g,y) != lam(srt, db0), y == a, ap(ap(h,y),z) != lam(srt, db0), ap(f,y) != b });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, clause({ ap(f_hol(),y) != troo, y == a, ap(ap(g_hol(),z),y) != troo, ap(f,y) != b }));
}

TEST_FUN(constraints_3) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ y == a, ap(ap(h,y),z) != lam(srt, db0), ap(f,y) != b });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, clause({ y == a, ap(ap(f_hol(),z),y) != troo, ap(f,y) != b }));
}

TEST_FUN(constraints_different) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ ap(g,y) != lam(srt, db0), y == a });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, clause({ ap(f_hol(),y) != troo, y == a }));

  auto d1 = clause({ ap(ap(h,z),b) != lam(srt, db0), ap(f,y) != b });
  auto d2 = handler.handleClause(d1);

  checkEqual(d2, clause({ ap(g_hol(),z) != troo, ap(f,y) != b }));
}

TEST_FUN(constraints_same) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ ap(g,y) != lam(srt, db0), y == a });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, clause({ ap(f_hol(),y) != troo, y == a }));

  auto d1 = clause({ ap(g,z) != lam(srt, db0), ap(f,y) != b });
  auto d2 = handler.handleClause(d1);

  checkEqual(d2, clause({ ap(f_hol(),z) != troo, ap(f,y) != b }));
}

TEST_FUN(constraints_flexflex) {
  PREAMBLE_HANDLER;
  auto c1 = clause({ ap(ys,a) != ap(zs,b), lam(srt, zs) != lam(srt, ys), ap(g,y) != lam(srt, db0) });
  auto c2 = handler.handleClause(c1);

  checkEqual(c2, clause({ ap(ys,a) != ap(zs,b), lam(srt, zs) != lam(srt, ys), ap(f_hol(),y) != troo }));
}

void testUnifier(Literal* constraint, Literal* def, Stack<LiteralStack> expected)
{
  unsigned nextVar = iterTraits(VariableIterator(constraint)).map([](auto t){ return t.var(); }).max().unwrapOr(0)+1;
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
  ap(ap(xs, a), b) == ap(ap(g, b), a), p(xs),
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
  g() == g(), p(xs),
  Stack<LiteralStack>{
    LiteralStack{ p(xs) },
  }
)

TEST_UNIFIER(constraints_iteration_3,
  g() == g1(), p(xs),
  Stack<LiteralStack>{
    LiteralStack(),
  }
)

TEST_UNIFIER(constraints_iteration_4,
  g() == lam(srt, ap(g, db0)), p(xs),
  Stack<LiteralStack>{
    LiteralStack{ p(xs) },
  }
)

TEST_UNIFIER(constraints_iteration_5,
  a == ap(ap(xs, b), c), p(xs),
  Stack<LiteralStack>{
    LiteralStack(),
    LiteralStack{ p(lam(srt, lam(srt, a))) },
  }
)

TEST_UNIFIER(constraints_iteration_6,
  g() == lam(srt, ap(g, a)), p(xs),
  Stack<LiteralStack>{
    LiteralStack(),
    LiteralStack(),
  }
)

TEST_UNIFIER(constraints_iteration_7,
  lam(srt, ap(g, x)) == lam(srt, ap(g, y)), q(x,y),
  Stack<LiteralStack>{
    LiteralStack(),
    LiteralStack{ lam(srt,x) != lam(srt,y), q(x,y) },
    // TODO we should get rid of unnecessary lambda enclosures in the solutions and get the following:
    // LiteralStack{ x != y, q(x,y) },
  }
)

TEST_UNIFIER(constraints_iteration_8,
  lam(srt, ap(f, ap(ys, db0))) == lam(srt, ap(f, ap(zs, db0))), q(ys,zs),
  Stack<LiteralStack>{
    LiteralStack(),
    LiteralStack{ ys != zs, q(ys,zs) },
  }
)
