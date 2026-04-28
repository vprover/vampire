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
  DECL_CONST(g, arrow(arrow(srt, Bool), srt))      \
  DECL_CONST(h, arrow({srt, srt}, srt))            \
  DECL_CONST(a, arrow(srt, Bool))                  \
  DECL_CONST(b, arrow(srt, Bool))                  \
  DECL_CONST(c, srt)

#define MY_GEN_RULE   Choice
#define MY_GEN_TESTER Generation::GenerationTester

// not done for non-selected literals
TEST_GENERATION(rule_fail_1,
    env.signature->addChoiceOperator(f.functor());
    env.signature->addChoiceOperator(g.functor());
    Generation::AsymmetricTest()
      .input( clause({ ap(f, a) == c }))
      .expected(none())
    )

// not done for non-choice operators
TEST_GENERATION(rule_fail_2,
    env.signature->addChoiceOperator(g.functor());
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(f, a) == c) }))
      .expected(none())
    )

// not done for variable arguments
TEST_GENERATION(rule_fail_3,
    env.signature->addChoiceOperator(f.functor());
    env.signature->addChoiceOperator(g.functor());
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(f, x) == c) }))
      .expected(none())
    )

// not done for variable heads with no choice operators
TEST_GENERATION(rule_fail_4,
    Generation::AsymmetricTest()
    .input( clause({ selected(ap(x.sort(arrow(arrow(srt, Bool), srt)), a) == c) }))
    .expected(none())
    )

TEST_GENERATION(rule_success_1,
    env.signature->addChoiceOperator(f.functor());
    env.signature->addChoiceOperator(g.functor());
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(f, a) == c) }))
      .expected(exactly(clause({ ap(a, y) == fols, ap(a, ap(f, a)) == troo })))
    )

TEST_GENERATION(rule_success_2,
    env.signature->addChoiceOperator(f.functor());
    env.signature->addChoiceOperator(g.functor());
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(x.sort(arrow(arrow(srt, Bool), srt)), a) == c) }))
      .expected(exactly(
        clause({ ap(a, y) == fols, ap(a, ap(f, a)) == troo }),
        clause({ ap(a, y) == fols, ap(a, ap(g, a)) == troo })
      ))
    )

TEST_GENERATION(rule_success_3,
    env.signature->addChoiceOperator(f.functor());
    env.signature->addChoiceOperator(g.functor());
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(h, {x, ap(f, a)}) != ap(h, {c, ap(y.sort(arrow(arrow(srt, Bool), srt)), b)})) }))
      .expected(exactly(
        clause({ ap(a, y) == fols, ap(a, ap(f, a)) == troo }),
        clause({ ap(b, y) == fols, ap(b, ap(f, b)) == troo }),
        clause({ ap(b, y) == fols, ap(b, ap(g, b)) == troo })
      ))
    )

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
