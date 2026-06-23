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
#include "Kernel/TermIterators.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"
#include <initializer_list>

using namespace Saturation;
using namespace Test;

#define MY_SYNTAX_SUGAR                               \
  DECL_SORT(s)                                        \
  DECL_DEFAULT_VARS                                   \
  DECL_CONST(f, arrow(s, s))                          \
  DECL_CONST(g, arrow({s, s}, s))                     \
  DECL_CONST(g1, arrow({s, s}, s))                    \
  DECL_CONST(h, arrow({arrow(s, s), arrow(s, s)}, s)) \
  DECL_CONST(h1, arrow({s, arrow(s, s)}, s))          \
  DECL_DE_BRUIJN_INDEX(db0, 0, s)                     \
  DECL_DE_BRUIJN_INDEX(db1, 1, s)                     \
  DECL_DE_BRUIJN_INDEX(db0_, 0, arrow(s,s))           \
  DECL_DE_BRUIJN_INDEX(db1_, 1, arrow(s,s))           \
  DECL_CONST(a, s)                                    \
  DECL_CONST(b, s)                                    \
  DECL_CONST(c, s)                                    \

#define LEFT_BANK 0
#define RIGHT_BANK 1
#define UNIF_DEPTH 3

struct ResultSpec {
  Stack<std::pair<VarSpec, TermList>> varSpecs;
  LiteralStack constraints;
};

auto vs(TermList var, unsigned index, TermList t)
{ return std::make_pair(VarSpec(var, index), t); }

auto vsLeft(TermList var, TermList t) { return vs(var, LEFT_BANK, t); }
auto vsRight(TermList var, TermList t) { return vs(var, RIGHT_BANK, t); }

template<bool funcExt>
void testUnifySuccess(TermList lhs, TermList rhs, Stack<ResultSpec> expected) {

  AbstractionOracle oracle(Shell::Options::UnificationWithAbstraction::HOL);
  AbstractingUnifier unif(oracle);

  if (!unif.unify(lhs, LEFT_BANK, rhs, RIGHT_BANK, /*fixedPointIteration=*/true)) {
    std::cout << std::endl;
    std::cout << "does not FO unify: " << lhs << " != " << rhs << std::endl;
    ASSERTION_VIOLATION;
  }

  HOL::AbstractingWrapper wrapper(&unif, UNIF_DEPTH, funcExt);
  for (unsigned i = 0; i < expected.size(); i++) {
    if (!wrapper.hasNext()) {
      std::cout << std::endl;
      std::cout << "unifier " << i << " is missing (unification " << lhs << " = " << rhs << ")" << std::endl;
      ASSERTION_VIOLATION;
    }
    auto hoUnif = wrapper.next();
    auto& e = expected[i];

    DHSet<VarSpec> vars;
    auto loadVars = [&vars](TermList t, unsigned index) {
      if (t.isVar()) {
        vars.insert(VarSpec(t, index));
      } else {
        vars.loadFromIterator(iterTraits(VariableIterator(t.term()))
          .map([index](TermList var) {return VarSpec(var, index); }));
      }
    };
    loadVars(lhs, LEFT_BANK);
    loadVars(rhs, RIGHT_BANK);

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
      vars.remove(vs);
    }
    ASS_REP(vars.isEmpty(), vars);

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
    if (cons.size() > e.constraints.size()) {
      std::cout << std::endl;
      std::cout << "unexpected constraint (" << i << "): " << *cons[e.constraints.size()] << " (unification " << lhs << " = " << rhs << ")" << std::endl;
      ASSERTION_VIOLATION;
    }
  }
  if (wrapper.hasNext()) {
    std::cout << std::endl;
    std::cout << "unexpected extra unifier (unification " << lhs << " = " << rhs << ")" << std::endl;
    ASSERTION_VIOLATION;
  }
}

template<bool funcExt>
void testUnifyFail(TermList lhs, TermList rhs) {

  AbstractionOracle oracle(Shell::Options::UnificationWithAbstraction::HOL);
  AbstractingUnifier unif(oracle);

  // we require the term to at least FO unify, maybe with abstraction
  if (!unif.unify(lhs, LEFT_BANK, rhs, RIGHT_BANK, /*fixedPointIteration=*/true)) {
    std::cout << std::endl;
    std::cout << "expected to FO unify: " << lhs << " != " << rhs << std::endl;
    ASSERTION_VIOLATION;
  }

  HOL::AbstractingWrapper wrapper(&unif, UNIF_DEPTH, funcExt);
  if (wrapper.hasNext()) {
    std::cout << std::endl;
    std::cout << "expected *not* to HO unify: " << lhs << " == " << rhs << std::endl;
    ASSERTION_VIOLATION;
  }
}

#define TEST_UNIFY_SUCCESS(name, lhs, rhs, ...)     \
  TEST_FUN(name) {                                  \
    env.setHigherOrder(true);                       \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR);                \
    testUnifySuccess<false>(lhs, rhs, __VA_ARGS__); \
  }

#define TEST_UNIFY_FAIL(name, lhs, rhs)             \
  TEST_FUN(name) {                                  \
    env.setHigherOrder(true);                       \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR);                \
    testUnifyFail<false>(lhs, rhs);                 \
  }

TEST_UNIFY_SUCCESS(success_1,
  ap(ap(x.sort(arrow({ s, s }, s)), a), b),
  ap(g, {b, a}),
  {
    {
      { vsLeft(x, lam(s, lam(s, ap(g, {db0, db1})))) },
      LiteralStack{},
    },
    {
      { vsLeft(x, lam(s, lam(s, ap(g, {b, db1})))) },
      LiteralStack{},
    },
    {
      { vsLeft(x, lam(s, lam(s, ap(g, {db0, a})))) },
      LiteralStack{},
    },
    { 
      { vsLeft(x, lam(s, lam(s, ap(g, {b, a})))) },
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
      { vsRight(x, lam(s, lam(s, a))) },
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
        vsLeft(x, x),
        vsRight(y, y)
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
        vsLeft(x, x),
        vsRight(x, y)
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
        vsLeft(x, x),
        vsRight(x, y)
      },
      { lam(s,ap(x.sort(arrow(s,s)), a)) != lam(s,ap(y.sort(arrow(s,s)), b)) },
    }
  }
)

TEST_UNIFY_SUCCESS(success_8,
  lam(s, db0),
  lam(s, ap(x.sort(arrow(s,s)), db0)),
  {
    ResultSpec{
      {
        vsRight(x, lam(s, db0))
      },
      LiteralStack{},
    }
  }
)

TEST_UNIFY_SUCCESS(success_9,
  lam(arrow(s,s), db0_),
  lam(arrow(s,s), lam(s, ap(db1_, db0))),
  {
    ResultSpec(),
  }
)

TEST_UNIFY_SUCCESS(success_10,
  ap(h, {x, lam(s, ap(x.sort(arrow(s,s)), ap(g, {y, db0})))}),
  ap(h, {lam(s, ap(g1, {db0, z})), lam(s, ap(g1, {ap(g, {a, db0}), z}))}),
  {
    ResultSpec{
      {
        vsLeft(x, lam(s, ap(g1, {db0, x}))),
        vsLeft(y, a),
        vsRight(z, x)
      },
      LiteralStack(),
    }
  }
)

TEST_UNIFY_SUCCESS(success_11,
  ap(ap(x.sort(arrow({s, s}, s)), b), a),
  ap(g, {a, b}),
  {
    ResultSpec{
      {
        vsLeft(x, lam(s, lam(s, ap(g, {db0, db1}))))
      },
      LiteralStack(),
    },
    ResultSpec{
      {
        vsLeft(x, lam(s, lam(s, ap(g, {a, db1}))))
      },
      LiteralStack(),
    },
    ResultSpec{
      {
        vsLeft(x, lam(s, lam(s, ap(g, {db0, b}))))
      },
      LiteralStack(),
    },
    ResultSpec{
      {
        vsLeft(x, lam(s, lam(s, ap(g, {a, b}))))
      },
      LiteralStack(),
    }
  }
)

TEST_UNIFY_SUCCESS(success_12,
  ap(ap(x.sort(arrow({arrow(s, s), s}, s)), lam(s, db0)), a),
  a,
  {
    ResultSpec{
      {
        vsLeft(x, lam(arrow(s,s), lam(s, ap(db1_, ap(db1_, ap(db1_, ap(ap(x.sort(arrow({arrow(s, s), s}, s)), db1_), db0)))))))
      },
      LiteralStack{
        a != ap(ap(x.sort(arrow({arrow(s, s), s}, s)), lam(s, db0)), a)
      },
    },
    ResultSpec{
      {
        vsLeft(x, lam(arrow(s,s), lam(s, ap(db1_, ap(db1_, db0)))))
      },
      LiteralStack(),
    },
    ResultSpec{
      {
        vsLeft(x, lam(arrow(s,s), lam(s, ap(db1_, ap(db1_, a)))))
      },
      LiteralStack(),
    },
    ResultSpec{
      {
        vsLeft(x, lam(arrow(s,s), db0_))
      },
      LiteralStack(),
    },
    ResultSpec{
      {
        vsLeft(x, lam(arrow(s,s), lam(s, ap(db1_, a))))
      },
      LiteralStack(),
    },
    ResultSpec{
      {
        vsLeft(x, lam(arrow(s,s), lam(s, db0)))
      },
      LiteralStack(),
    },
    ResultSpec{
      {
        vsLeft(x, lam(arrow(s,s), lam(s, a)))
      },
      LiteralStack(),
    }
  }
)

TEST_UNIFY_SUCCESS(success_13,
  ap(h1, {ap(x.sort(arrow(s,s)), ap(g, {y, db0})), x}),
  ap(h1, {ap(g1, {ap(g, {a, db0}), z}), lam(s, ap(g1, {db0, z}))}),
  {
    ResultSpec{
      {
        vsLeft(x, lam(s, ap(g1, {db0, x}))),
        vsLeft(y, a),
        vsRight(z, x)
      },
      LiteralStack(),
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

TEST_UNIFY_FAIL(fail_3,
  lam(s, db0),
  lam(s, x.sort(s))
)

TEST_UNIFY_FAIL(fail_4,
  ap(h, {x, lam(s, ap(x.sort(arrow(s,s)), ap(g, {y, db0})))}),
  ap(h, {lam(s, ap(g1, {db0, z})), ap(g1, a)})
)

TEST_UNIFY_FAIL(fail_5,
  ap(h, {x, lam(s, ap(x.sort(arrow(s,s)), ap(g, {y, db0})))}),
  ap(h, {lam(s, ap(g1, {db0, z})), lam(s, ap(g1, {db0, db0}))})
)

TEST_UNIFY_FAIL(fail_6,
  ap(h, {x, lam(s, ap(x.sort(arrow(s,s)), ap(g, {y, db0})))}),
  ap(h, {lam(s, ap(g1, {db0, z})), ap(g1, ap(g, {a, b}))})
)

TEST_UNIFY_FAIL(fail_7,
  ap(h, {x, lam(s, ap(x.sort(arrow(s,s)), ap(g, {y, db0})))}),
  ap(h, {lam(s, ap(g1, {db0, z})), lam(s, ap(g1, {ap(g, {a, db0}), db0}))})
)
