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
#include "Inferences/HOL/BoolSimp.hpp"

#include "Test/SimplificationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_SORT(srt)                                   \
  DECL_SORT_BOOL                                   \
  DECL_DEFAULT_VARS                                \
  TROO                                             \
  FOLS                                             \
  DECL_NOT_PROXY                                   \
  DECL_AND_PROXY                                   \
  DECL_OR_PROXY                                    \
  DECL_IMP_PROXY                                   \
  DECL_IFF_PROXY                                   \
  DECL_EQ_PROXY                                    \
  DECL_CONST(f, arrow(Bool, srt))                  \
  DECL_CONST(g, arrow({srt, srt}, srt))            \
  DECL_CONST(h, arrow(srt, Bool))                  \
  DECL_DE_BRUIJN_INDEX(db0, 0, Bool)               \
  DECL_CONST(a, srt)                               \
  DECL_CONST(b, srt)

#define MY_SIMPL_RULE   BoolSimp
#define MY_SIMPL_TESTER Simplification::SimplificationTester

TEST_SIMPLIFY(fail_1,
    Simplification::NotApplicable()
      .input(clause({ ap(g, {a, b}) == a, ap(f, x) != y }))
    )

// partially applied proxy terms are not simplified
TEST_SIMPLIFY(fail_2,
    Simplification::NotApplicable()
      .input(clause({ ap(andP, troo) != ap(orP, fols), ap(iffP, ap(h, a)) == ap(impP, ap(h, b)) }))
    )

// conjunction
TEST_SIMPLIFY(and_fail_1,
    Simplification::NotApplicable()
      .input(clause({ ap(f, ap(andP, {ap(h, a), ap(notP, ap(h, x))})) != a }))
    )

TEST_SIMPLIFY(and_success_1,
    Simplification::Success()
      .input(clause({ ap(f, ap(andP, {troo, ap(h, a)})) != a }))
      .expected(clause({ ap(f, ap(h, a)) != a }))
    )

TEST_SIMPLIFY(and_success_2,
    Simplification::Success()
      .input(clause({ ap(f, ap(andP, {ap(h, a), troo})) != a }))
      .expected(clause({ ap(f, ap(h, a)) != a }))
    )

TEST_SIMPLIFY(and_success_3,
    Simplification::Success()
      .input(clause({ ap(f, ap(andP, {fols, ap(h, a)})) != a }))
      .expected(clause({ ap(f, fols) != a }))
    )

TEST_SIMPLIFY(and_success_4,
    Simplification::Success()
      .input(clause({ ap(f, ap(andP, {ap(h, a), fols})) != a }))
      .expected(clause({ ap(f, fols) != a }))
    )

TEST_SIMPLIFY(and_success_5,
    Simplification::Success()
      .input(clause({ ap(f, ap(andP, {ap(h, a), ap(notP, ap(h, a))})) != a }))
      .expected(clause({ ap(f, fols) != a }))
    )

// disjunction
TEST_SIMPLIFY(or_fail_1,
    Simplification::NotApplicable()
      .input(clause({ ap(f, ap(orP, {ap(h, a), ap(notP, ap(h, x))})) != a }))
    )

TEST_SIMPLIFY(or_success_1,
    Simplification::Success()
      .input(clause({ ap(f, ap(orP, {troo, ap(h, a)})) != a }))
      .expected(clause({ ap(f, troo) != a }))
    )

TEST_SIMPLIFY(or_success_2,
    Simplification::Success()
      .input(clause({ ap(f, ap(orP, {ap(h, a), troo})) != a }))
      .expected(clause({ ap(f, troo) != a }))
    )

TEST_SIMPLIFY(or_success_3,
    Simplification::Success()
      .input(clause({ ap(f, ap(orP, {fols, ap(h, a)})) != a }))
      .expected(clause({ ap(f, ap(h, a)) != a }))
    )

TEST_SIMPLIFY(or_success_4,
    Simplification::Success()
      .input(clause({ ap(f, ap(orP, {ap(h, a), fols})) != a }))
      .expected(clause({ ap(f, ap(h, a)) != a }))
    )

TEST_SIMPLIFY(or_success_5,
    Simplification::Success()
      .input(clause({ ap(f, ap(orP, {ap(h, a), ap(notP, ap(h, a))})) != a }))
      .expected(clause({ ap(f, troo) != a }))
    )

TEST_SIMPLIFY(or_success_6,
    Simplification::Success()
      .input(clause({ ap(f, ap(orP, {ap(notP, ap(h, x)), ap(h, x)})) != a }))
      .expected(clause({ ap(f, troo) != a }))
    )

// implication
TEST_SIMPLIFY(imp_fail_1,
    Simplification::NotApplicable()
      .input(clause({ ap(f, ap(impP, {ap(h, a), ap(notP, ap(h, x))})) != a }))
    )

TEST_SIMPLIFY(imp_success_1,
    Simplification::Success()
      .input(clause({ ap(f, ap(impP, {troo, ap(h, a)})) != a }))
      .expected(clause({ ap(f, ap(h, a)) != a }))
    )

TEST_SIMPLIFY(imp_success_2,
    Simplification::Success()
      .input(clause({ ap(f, ap(impP, {ap(h, a), troo})) != a }))
      .expected(clause({ ap(f, troo) != a }))
    )

TEST_SIMPLIFY(imp_success_3,
    Simplification::Success()
      .input(clause({ ap(f, ap(impP, {fols, ap(h, a)})) != a }))
      .expected(clause({ ap(f, troo) != a }))
    )

TEST_SIMPLIFY(imp_success_4,
    Simplification::Success()
      .input(clause({ ap(f, ap(impP, {ap(h, a), fols})) != a }))
      .expected(clause({ ap(f, ap(notP, ap(h, a))) != a }))
    )

TEST_SIMPLIFY(imp_success_5,
    Simplification::Success()
      .input(clause({ ap(f, ap(impP, {ap(h, a), ap(h, a)})) != a }))
      .expected(clause({ ap(f, troo) != a }))
    )

TEST_SIMPLIFY(imp_success_6,
    Simplification::Success()
      .input(clause({ ap(f, ap(impP, {ap(notP, ap(h, a)), ap(h, a)})) != a }))
      .expected(clause({ ap(f, ap(h, a)) != a }))
    )

TEST_SIMPLIFY(imp_success_7,
    Simplification::Success()
      .input(clause({ ap(f, ap(impP, {ap(h, a), ap(notP, ap(h, a))})) != a }))
      .expected(clause({ ap(f, ap(notP, ap(h, a))) != a }))
    )

// equivalence
TEST_SIMPLIFY(iff_fail_1,
    Simplification::NotApplicable()
      .input(clause({ ap(f, ap(iffP, {ap(h, a), ap(notP, ap(h, x))})) != a }))
    )

TEST_SIMPLIFY(iff_success_1,
    Simplification::Success()
      .input(clause({ ap(f, ap(iffP, {troo, ap(h, a)})) != a }))
      .expected(clause({ ap(f, ap(h, a)) != a }))
    )

TEST_SIMPLIFY(iff_success_2,
    Simplification::Success()
      .input(clause({ ap(f, ap(iffP, {ap(h, a), troo})) != a }))
      .expected(clause({ ap(f, ap(h, a)) != a }))
    )

TEST_SIMPLIFY(iff_success_3,
    Simplification::Success()
      .input(clause({ ap(f, ap(iffP, {fols, ap(h, a)})) != a }))
      .expected(clause({ ap(f, ap(notP, ap(h, a))) != a }))
    )

TEST_SIMPLIFY(iff_success_4,
    Simplification::Success()
      .input(clause({ ap(f, ap(iffP, {ap(h, a), fols})) != a }))
      .expected(clause({ ap(f, ap(notP, ap(h, a))) != a }))
    )

TEST_SIMPLIFY(iff_success_5,
    Simplification::Success()
      .input(clause({ ap(f, ap(iffP, {ap(h, a), ap(h, a)})) != a }))
      .expected(clause({ ap(f, troo) != a }))
    )

TEST_SIMPLIFY(iff_success_6,
    Simplification::Success()
      .input(clause({ ap(f, ap(iffP, {ap(notP, ap(h, a)), ap(h, a)})) != a }))
      .expected(clause({ ap(f, fols) != a }))
    )

TEST_SIMPLIFY(iff_success_7,
    Simplification::Success()
      .input(clause({ ap(f, ap(iffP, {ap(h, a), ap(notP, ap(h, a))})) != a }))
      .expected(clause({ ap(f, fols) != a }))
    )

// negation
TEST_SIMPLIFY(not_fail_1,
    Simplification::NotApplicable()
      .input(clause({ ap(f, ap(notP, ap(h, a))) != a }))
    )

TEST_SIMPLIFY(not_success_1,
    Simplification::Success()
      .input(clause({ ap(f, ap(notP, troo)) != a }))
      .expected(clause({ ap(f, fols) != a }))
    )

TEST_SIMPLIFY(not_success_2,
    Simplification::Success()
      .input(clause({ ap(f, ap(notP, fols)) != a }))
      .expected(clause({ ap(f, troo) != a }))
    )

TEST_SIMPLIFY(not_success_3,
    Simplification::Success()
      .input(clause({ ap(f, ap(notP, ap(notP, ap(h, a)))) != a }))
      .expected(clause({ ap(f, ap(h, a)) != a }))
    )

// equality
TEST_SIMPLIFY(eq_fail_1,
    Simplification::NotApplicable()
      .input(clause({ ap(f, ap(eqP(srt), {a, b})) != a }))
    )

TEST_SIMPLIFY(eq_success_1,
    Simplification::Success()
      .input(clause({ ap(f, ap(eqP(srt), {a, a})) != a }))
      .expected(clause({ ap(f, troo) != a }))
    )

// only first found term is simplified
TEST_SIMPLIFY(success_1,
    Simplification::Success()
      .input(clause({ ap(f, ap(orP, {troo, ap(h, a)})) != x, y != ap(f, ap(andP, {troo, ap(h, a)})) }))
      .expected(clause({ ap(f, troo) != x, y != ap(f, ap(andP, {troo, ap(h, a)})) }))
    )

// expressions inside lambdas with potentially DB indices are simplified
TEST_SIMPLIFY(success_2,
    Simplification::Success()
      .input(clause({ lam(Bool, ap(f, ap(andP, {troo, db0}))) != x }))
      .expected(clause({ lam(Bool, ap(f, db0)) != x }))
    )
