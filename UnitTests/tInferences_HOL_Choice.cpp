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
#include "Inferences/Choice.hpp"
#include "Inferences/InferenceEngine.hpp"

#include "Test/GenerationTester.hpp"
#include "Test/SimplificationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_SORT(srt)                                   \
  DECL_SORT_BOOL                                   \
  DECL_DEFAULT_VARS                                \
  DECL_VAR_SORTED(xs, 0, arrow(srt, Bool))         \
  TROO                                             \
  FOLS                                             \
  DECL_PRED(p, { srt })                            \
  DECL_CONST(f, arrow(arrow(srt, Bool), srt))      \
  DECL_POLY_CONST(g2, 1, x)                        \
  DECL_POLY_CONST(g3, 1, x)                        \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                \
  DECL_CONST(a, srt)                               \
  DECL_CONST(b, srt)

#define MY_GEN_RULE   Choice
#define MY_GEN_TESTER Generation::GenerationTester

// TEST_GENERATION(fail_1,
//     Generation::AsymmetricTest()
//       .input( clause({ selected(x == y), g == lam(srt, ap(f, {db0, db0})) }))
//       .expected(none())
//     )

// TEST_GENERATION(success_1,
//     Generation::AsymmetricTest()
//       .input( clause({ selected(g == lam(srt, ap(f, {x, x}))) }))
//       .expected(exactly(clause({ ap(g, y) == ap(lam(srt, ap(f, {x, x})), y) })))
//     )

#define MY_SIMPL_RULE   ChoiceDefinitionISE
#define MY_SIMPL_TESTER Simplification::SimplificationTester

// nothing happens with one literal
TEST_SIMPLIFY(fail_1,
    Simplification::NotApplicable()
      .input(clause({ ap(xs, y) == fols }))
    )

TEST_SIMPLIFY(fail_2,
    Simplification::NotApplicable()
      .input(clause({ ap(xs, y) == troo }))
    )

TEST_SIMPLIFY(fail_3,
    Simplification::NotApplicable()
      .input(clause({ ap(xs, y) != fols }))
    )

TEST_SIMPLIFY(fail_4,
    Simplification::NotApplicable()
      .input(clause({ ap(xs, y) != troo }))
    )

TEST_SIMPLIFY(fail_5,
    Simplification::NotApplicable()
      .input(clause({ ap(xs, ap(f, xs)) == troo }))
    )

TEST_SIMPLIFY(fail_6,
    Simplification::NotApplicable()
      .input(clause({ ap(xs, ap(f, xs)) != troo }))
    )

TEST_SIMPLIFY(fail_7,
    Simplification::NotApplicable()
      .input(clause({ ap(xs, ap(f, xs)) == fols }))
    )

TEST_SIMPLIFY(fail_8,
    Simplification::NotApplicable()
      .input(clause({ ap(xs, ap(f, xs)) != fols }))
    )

// wrong polarities
TEST_SIMPLIFY(fail_9,
    Simplification::NotApplicable()
      .input(clause({ ap(xs, y) == troo, ap(xs, ap(f, xs)) == troo, }))
    )

TEST_SIMPLIFY(fail_10,
    Simplification::NotApplicable()
      .input(clause({ ap(xs, y) == fols, ap(xs, ap(f, xs)) == fols, }))
    )

TEST_SIMPLIFY(success_1,
    Simplification::Success()
      .input(clause({ ap(xs, y) == fols, ap(xs, ap(f, xs)) == troo, }))
      .expected(Simplification::Redundant{})
    )

TEST_SIMPLIFY(success_2,
    Simplification::Success()
      .input(clause({ ap(xs, ap(f, xs)) == troo, ap(xs, z) != troo, }))
      .expected(Simplification::Redundant{})
    )
