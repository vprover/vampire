/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/SyntaxSugar.hpp"
#include "Inferences/SubsumptionEqualityResolution.hpp"

#include "Test/SimplificationTester.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

namespace {

#define MY_SIMPL_RULE   SubsumptionEqualityResolution
#define MY_SIMPL_TESTER Simplification::SimplificationTester

#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_VAR(u, 3)                                                                                              \
  DECL_SORT(s)                                                                                                \
  DECL_FUNC(f, {s, s}, s)                                                                                     \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})

// not applicable to positive literals or non-equalities
TEST_SIMPLIFY(fail01,
  Simplification::NotApplicable()
    .input(clause({ p(g(x)), y.sort(s) == z, ~q(u) }))
  )

// not applicable if not renaming on the rest of literals
TEST_SIMPLIFY(fail02,
  Simplification::NotApplicable()
    .input(clause({ f(x,y) != f(a,g(z)), p(x), ~p(y) }))
  )

// not applicable if not renaming on the rest of literals
TEST_SIMPLIFY(fail03,
  Simplification::NotApplicable()
    .input(clause({ x.sort(s) != y, p(x), ~p(y) }))
  )

// applicable to some negative equations
TEST_SIMPLIFY(success01,
  Simplification::Success()
    .input(clause({ f(a,y) != f(x,g(z)) }))
    .expected(clause({ }))
)

// applicable despite variable being bound
TEST_SIMPLIFY(success02,
  Simplification::Success()
    .input(clause({ ~p(y), f(x,y) != f(x,x) }))
    .expected(clause({ ~p(y) }))
  )

// applicable to some negative equations and other literals
TEST_SIMPLIFY(success03,
  Simplification::Success()
    .input(clause({ p(z), f(f(z,u),y) != f(x,g(z)), q(f(u,z)) }))
    .expected(clause({ p(z), q(f(u,z)) }))
)

}