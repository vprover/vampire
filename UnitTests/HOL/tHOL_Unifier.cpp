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
#include "Forwards.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/HOL/Unifier.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"
#include <initializer_list>

using namespace Saturation;
using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_APP                                         \
  DECL_LAM                                         \
  DECL_SORT(s)                                     \
  DECL_SORT(srt2)                                  \
  DECL_SORT_BOOL                                   \
  TROO                                             \
  DECL_DEFAULT_VARS                                \
  DECL_CONST(f, arrow(s, s))                       \
  DECL_CONST(g, arrow({s, s}, s))                  \
  DECL_CONST(g1, arrow({s, s}, s))                 \
  DECL_CONST(h, arrow({s, s, s}, s))               \
  DECL_CONST(f2, arrow({s, srt2}, Bool))           \
  DECL_DE_BRUIJN_INDEX(db0, 0, s)                  \
  DECL_DE_BRUIJN_INDEX(db1, 1, s)                  \
  DECL_CONST(a, s)                                 \
  DECL_CONST(b, s)                                 \
  DECL_CONST(c, s)                                 \
  DECL_CONST(d, srt2)                              \

#define LEFT_BANK 0
#define RIGHT_BANK 1

struct ResultSpec {
  Stack<std::pair<VarSpec, TermList>> varSpecs;
  LiteralStack constraints;
};

std::pair<VarSpec, TermList> vs(unsigned var, unsigned index, TermList t) {
  return { VarSpec(TermList::var(var), index), t };
}

void testUnifySuccess(TermList lhs, TermList rhs, Stack<ResultSpec> expected) {

  AbstractionOracle oracle(Shell::Options::UnificationWithAbstraction::HOL);
  AbstractingUnifier unif(oracle);

  if (!unif.unify(lhs, LEFT_BANK, rhs, RIGHT_BANK, /*fixedPointIteration=*/true)) {
    std::cout << std::endl;
    std::cout << "does not FO unify: " << lhs << " != " << rhs << std::endl;
    ASSERTION_VIOLATION;
  }

  HOL::AbstractingWrapper wrapper(&unif, 10);
  for (unsigned i = 0; i < expected.size(); i++) {
    if (!wrapper.hasNext()) {
      std::cout << std::endl;
      std::cout << "unifier " << i << " is missing (unification " << lhs << " = " << rhs << ")" << std::endl;
      ASSERTION_VIOLATION;
    }
    auto hoUnif = wrapper.next();
    auto& e = expected[i];

    for (const auto& [vs, exp] : e.varSpecs) {
      auto act = HOL::reduce::betaEtaNF(hoUnif->subs().apply(vs.varAsTermlist(), vs.index));
      if (act != exp) {
        std::cout << std::endl;
        std::cout << "unifier " << i << ", variable " << vs << " mismatch:" << std::endl;
        std::cout << "actual:   " << act << std::endl;
        std::cout << "expected: " << exp << std::endl;
        std::cout << "unification " << lhs << " = " << rhs << std::endl;
        ASSERTION_VIOLATION;
      }
    }

    auto cons = hoUnif->computeConstraintLiterals();
    for (unsigned j = 0; j < e.constraints.size(); j++) {
      if (j >= cons.size()) {
        std::cout << std::endl;
        std::cout << "missing constraint (unification " << lhs << " = " << rhs << ")" << std::endl;
        ASSERTION_VIOLATION;
      }
      if (cons[j] != e.constraints[j]) {
        std::cout << std::endl;
        std::cout << "unifier " << i << ", constraint " << j << " mismatch" << std::endl;
        std::cout << "actual:   " << *cons[j] << std::endl;
        std::cout << "expected: " << *e.constraints[j] << std::endl;
        std::cout << "unification " << lhs << " = " << rhs << std::endl;
        ASSERTION_VIOLATION;
      }
    }
  }
  if (wrapper.hasNext()) {
    std::cout << std::endl;
    std::cout << "unexpected extra unifier (unification " << lhs << " = " << rhs << ")" << std::endl;
    ASSERTION_VIOLATION;
  }
}

void testUnifyFail(TermList lhs, TermList rhs) {

  AbstractionOracle oracle(Shell::Options::UnificationWithAbstraction::HOL);
  AbstractingUnifier unif(oracle);

  // we require the term to at least FO unify, maybe with abstraction
  if (!unif.unify(lhs, LEFT_BANK, rhs, RIGHT_BANK, /*fixedPointIteration=*/true)) {
    std::cout << std::endl;
    std::cout << "does not FO unify: " << lhs << " != " << rhs << std::endl;
    ASSERTION_VIOLATION;
  }

  HOL::AbstractingWrapper wrapper(&unif, 10);
  if (wrapper.hasNext()) {
    std::cout << std::endl;
    std::cout << "HO unifies: " << lhs << " == " << rhs << std::endl;
    ASSERTION_VIOLATION;
  }
}

#define TEST_UNIFY_SUCCESS(name, lhs, rhs, ...) \
  TEST_FUN(name) {                              \
    env.setHigherOrder(true);                   \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR);            \
    testUnifySuccess(lhs, rhs, __VA_ARGS__);    \
  }

#define TEST_UNIFY_FAIL(name, lhs, rhs)         \
  TEST_FUN(name) {                              \
    env.setHigherOrder(true);                   \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR);            \
    testUnifyFail(lhs, rhs);                    \
  }

TEST_UNIFY_SUCCESS(success_1,
  ap(ap(x.sort(arrow({ s, s }, s)), a), b),
  ap(g, {b, a}),
  {
    {
      { vs(0, 0, lam(s, lam(s, ap(g, {db0, db1})))) },
      LiteralStack{},
    },
    {
      { vs(0, 0, lam(s, lam(s, ap(g, {b, db1})))) },
      LiteralStack{},
    },
    {
      { vs(0, 0, lam(s, lam(s, ap(g, {db0, a})))) },
      LiteralStack{},
    },
    { 
      { vs(0, 0, lam(s, lam(s, ap(g, {b, a})))) },
      LiteralStack{},
    }
  }
)

TEST_UNIFY_SUCCESS(success_2,
  g(),
  g(),
  {
    ResultSpec(),
  }
)

TEST_UNIFY_SUCCESS(success_3,
  g(),
  lam(s, ap(g, db0)),
  {
    ResultSpec(),
  }
)

TEST_UNIFY_SUCCESS(success_4,
  a,
  ap(ap(x.sort(arrow({s, s}, s)), b), c),
  {
    ResultSpec{
      { vs(0, 1, lam(s, lam(s, a))) },
      LiteralStack{},
    }
  }
)

TEST_UNIFY_SUCCESS(success_5,
  lam(s, ap(g, x)),
  lam(s, ap(g, y)),
  {
    ResultSpec{
      {
        vs(0, 0, x),
        vs(1, 1, y)
      },
      { lam(s,x.sort(s)) != lam(s,y.sort(s)) }
    },
  }
)

TEST_UNIFY_SUCCESS(success_6,
  lam(s, ap(f, ap(x.sort(arrow(s, s)), db0))),
  lam(s, ap(f, ap(x.sort(arrow(s, s)), db0))),
  {
    ResultSpec{
      {
        vs(0,0,x),
        vs(0,1,y)
      },
      { x.sort(arrow(s, s)) != y } },
  }
)

TEST_UNIFY_SUCCESS(success_7,
  lam(s, ap(f, ap(x.sort(arrow(s,s)), a))),
  lam(s, ap(f, ap(x.sort(arrow(s,s)), b))),
  {
    ResultSpec{
      {
        vs(0,0,x),
        vs(0,1,y)
      },
      { lam(s,ap(x.sort(arrow(s,s)), a)) != lam(s,ap(y.sort(arrow(s,s)), b)) },
    }
  }
)

TEST_UNIFY_FAIL(fail_1,
  lam(s, ap(g, db0)),
  lam(s, ap(g1, db0))
)

TEST_UNIFY_FAIL(fail_2,
  g(),
  lam(s, ap(g, a))
)
