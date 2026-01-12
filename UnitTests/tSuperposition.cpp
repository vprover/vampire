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
#include "Test/GenerationTester.hpp"

#include "Inferences/Superposition.hpp"

using namespace Test;

/**
 * NECESSARY: We need to tell the tester which syntax sugar to import for creating terms & clauses.
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_VAR(u, 3)                                                                                              \
  DECL_SORT(s)                                                                                                \
  DECL_FUNC(f, {s, s}, s)                                                                                     \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_CONST(b, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})                                                                                          \

REGISTER_GEN_TESTER(Generation::GenerationTester<Inferences::Superposition>(Superposition()))

// no superposition with negative equations
TEST_GENERATION(test_01,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(f(x,y) != x) }),
        clause({ selected(f(x,y) != y) })
      })
      .expected(none())
    )

// self superposition with equation
TEST_GENERATION(test_02,
    Generation::SymmetricTest()
      .inputs({ clause({ selected(f(f(x,y),z) == x) }) })
      .expected(exactly(clause({ f(x,y) == f(x,z) })))
    )

// superposition from variable
TEST_GENERATION(test_03,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(x == a), p(y), f(y,z) == g(z) }),
        clause({ selected(f(x,y) == g(z)) }),
      })
      .selfApplications(false)
      .expected(exactly(
        clause({ a == g(x), p(y), f(y,z) == g(z) }),
        clause({ f(x,y) == a, p(z), f(z,u) == g(u) })
      ))
    )

// superposition from variable is not performed due to variable in predicate
TEST_GENERATION(test_04,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(x == a), p(x) }),
        clause({ selected(f(x,y) == g(z)) }),
      })
      .selfApplications(false)
      .expected(none())
    )

// superposition from variable is not performed due to variable in function
TEST_GENERATION(test_05,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(x == a), g(x) == y }),
        clause({ selected(f(x,y) == g(z)) }),
      })
      .selfApplications(false)
      .expected(none())
    )

// superposition is not performed when lhs < rhs
TEST_GENERATION(test_06,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(f(x,y) == f(y,x)), g(x) == y }),
        clause({ selected(g(f(a,b)) != a) }),
      })
      .selfApplications(false)
      .expected(none())
    )

// superposition is not performed when lhs = rhs
TEST_GENERATION(test_07,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(f(x,y) == f(y,x)), g(x) == y }),
        clause({ selected(g(f(a,a)) != a) }),
      })
      .selfApplications(false)
      .expected(none())
    )

// superposition is not performed when a tautology would be generated
TEST_GENERATION(test_08,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(f(x,y) == y), g(x) == y }),
        clause({ selected(g(f(g(x),a)) == g(a)) }),
      })
      .selfApplications(false)
      .expected(none())
    )

// superposition is not performed when literal is not selected
TEST_GENERATION(test_09,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(f(x,y) == y), g(x) == y }),
        clause({ selected(~p(x)), p(f(x,y)) }),
      })
      .selfApplications(false)
      .expected(none())
    )

// simultaneous superposition
TEST_GENERATION(test_10,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(f(x,y) == y), g(x) == y }),
        clause({ selected(~p(f(x,y))), q(f(x,y)) }),
      })
      .selfApplications(false)
      .expected(exactly(clause({ ~p(y), q(y), g(x) == y })))
    )

// non-simultaneous superposition
TEST_GENERATION(test_11,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(f(x,y) == y), g(x) == y }),
        clause({ selected(~p(f(x,y))), q(f(x,y)) }),
      })
      .options({ { "simultaneous_superposition", "off" } })
      .selfApplications(false)
      .expected(exactly(clause({ ~p(y), q(f(x,y)), g(x) == y })))
    )

// superposition not performed due to trivial equality in superposed-from clause
TEST_GENERATION(test_12,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(g(x) == x), x == a }),
        clause({ selected(~p(g(a))) }),
      })
      .selfApplications(false)
      .expected(none())
    )

// superposition not performed due to trivial equality in superposed-into clause
TEST_GENERATION(test_13,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(g(a) == a) }),
        clause({ selected(~p(g(x))), x == a }),
      })
      .selfApplications(false)
      .expected(none())
    )

// superposition performed despite maximality aftercheck in superposed-into clause
TEST_GENERATION(test_14,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(f(b,a) == g(a)) }),
        clause({ selected(f(x,y) != x), selected(f(y,x) != y) }),
      })
      .selfApplications(false)
      .expected(exactly(
        clause({ g(a) != b, f(b,a) != a }),
        clause({ g(a) != b, f(b,a) != a })
      ))
    )

// superposition not performed due to maximality aftercheck in superposed-into clause
TEST_GENERATION(test_15,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(f(a,b) == g(a)) }),
        clause({ selected(f(x,y) != x), selected(f(y,x) != y) }),
      })
      .selfApplications(false)
      .expected(none())
    )

// superposition performed despite maximality aftercheck in superposed-from clause
TEST_GENERATION(test_16,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(f(x,y) == x), selected(f(y,x) == y) }),
        clause({ selected(~p(f(b,a))) }),
      })
      .selfApplications(false)
      .expected(exactly(
        clause({ ~p(b), f(a,b) == a }),
        clause({ ~p(b), f(a,b) == a })
      ))
    )

// superposition not performed due to maximality aftercheck in superposed-from clause
TEST_GENERATION(test_17,
    Generation::SymmetricTest()
      .inputs({
        clause({ selected(f(x,y) == x), selected(f(y,x) == y) }),
        clause({ selected(~p(f(a,b))) }),
      })
      .selfApplications(false)
      .expected(none())
    )

// TODO
// superposition with colors
// superposition only into bigger side of the equation