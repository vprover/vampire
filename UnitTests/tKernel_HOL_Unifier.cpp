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
#include "Kernel/HOL/Unifier.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/TestUtils.hpp"

using namespace Saturation;
using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_APP                                         \
  DECL_LAM                                         \
  DECL_SORT(srt)                                   \
  DECL_SORT(srt2)                                  \
  DECL_SORT_BOOL                                   \
  TROO                                             \
  DECL_VAR_SORTED(x, 0, srt)                       \
  DECL_VAR_SORTED(x2, 1, srt2)                     \
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
  DECL_CONST(f2, arrow({srt, srt2}, Bool))         \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                \
  DECL_DE_BRUIJN_INDEX(db1, 1, srt)                \
  DECL_CONST(a, srt)                               \
  DECL_CONST(b, srt)                               \
  DECL_CONST(c, srt)                               \
  DECL_CONST(d, srt2)                              \
  NEXT_INTRODUCED_FUN(f_hol,0)                     \
  NEXT_INTRODUCED_FUN(g_hol,1)

void testUnifier(Literal* constraint, Literal* def, Stack<LiteralStack> expected)
{
  unsigned nextVar = iterTraits(VariableIterator(constraint)).map([](auto t){ return t.var(); }).max().unwrapOr(0)+1;
  HOL::Unifier unifier(constraint, def, nextVar);

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
  ap(ap(xs, a), b) == ap(g, {b, a}), p(xs),
  Stack<LiteralStack>{
    LiteralStack(),
    LiteralStack(),
    LiteralStack(),
    LiteralStack(),
    LiteralStack{ p(lam(srt, lam(srt, ap(g, {db0, db1})))) },
    LiteralStack{ p(lam(srt, lam(srt, ap(g, {b, db1})))) },
    LiteralStack(),
    LiteralStack{ p(lam(srt, lam(srt, ap(g, {db0, a})))) },
    LiteralStack{ p(lam(srt, lam(srt, ap(g, {b, a})))) },
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

TEST_UNIFIER(constraints_iteration_9,
  lam(srt, ap(f, ap(ys, a))) == lam(srt, ap(f, ap(ys, b))), p(ys),
  Stack<LiteralStack>{
    LiteralStack(),
    LiteralStack{ lam(srt,ap(ys, a)) != lam(srt,ap(ys, b)), p(ys) },
  }
)
