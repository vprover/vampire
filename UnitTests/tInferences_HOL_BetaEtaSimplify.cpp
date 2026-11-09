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
#include "Inferences/HOL/BetaEtaSimplify.hpp"

#include "Test/SimplificationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                                       \
  DECL_SORT(srt)                                              \
  DECL_VAR_SORTED(x, 0, srt)                                  \
  DECL_VAR_SORTED(y, 1, srt)                                  \
  DECL_VAR_SORTED(z, 2, srt)                                  \
  DECL_VAR_SORTED(xs, 3, arrow({ srt, srt }, srt))            \
  DECL_FUNC(f, {srt, srt}, srt)                               \
  DECL_CONST(g, arrow({srt, srt}, srt))                       \
  DECL_CONST(g1, arrow({ arrow({srt, srt}, srt), srt }, srt)) \
  DECL_CONST(h, arrow({srt, srt}, srt))                       \
  DECL_CONST(h1, arrow(srt, srt))                             \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                           \
  DECL_DE_BRUIJN_INDEX(db1, 1, srt)                           \
  DECL_DE_BRUIJN_INDEX(db01, 0, arrow(srt, srt))              \
  DECL_DE_BRUIJN_INDEX(db11, 1, arrow(srt, srt))              \
  DECL_CONST(a, srt)                                          \
  DECL_CONST(b, srt)                                          \
  DECL_CONST(c, srt)

#define MY_SIMPL_RULE   BetaEtaSimplify
#define MY_SIMPL_TESTER Simplification::SimplificationTester

TEST_SIMPLIFY(fail_1,
    Simplification::NotApplicable()
      .input(clause({ x == y, f(x,y) != x }))
    )

// (\.\. g db1 db0) a b  ==>  g a b      (nested lambdas, two args, one with a compound term)
TEST_SIMPLIFY(success_1,
    Simplification::Success()
      .input(clause({ ap(lam(srt, lam(srt, ap(g, {db1, db0}))), {a, b}) != ap(lam(srt, ap(g, db0)), {f(x,y), b}) }))
      .expected(clause({ ap(g, {a, b}) != ap(g, {f(x,y), b}) }))
    )

TEST_SIMPLIFY(success_2,
    Simplification::Success()
      .input(clause({ f(x,y) == a, ap(lam(srt, ap(lam(srt, ap(g, db0)), db0)), a) != ap(lam(srt, ap(xs, z)), b) }))
      .expected(clause({ f(x,y) == a, ap(g, a) != ap(xs, z) }))
    )

// Unused bound variable: (\. a) b  ==>  a
TEST_SIMPLIFY(beta_unused_binder,
    Simplification::Success()
      .input(clause({ ap(lam(srt, a), {b}) != c }))
      .expected(clause({ a != c }))
    )

// Identity: (\. db0) a  ==>  a
TEST_SIMPLIFY(beta_identity,
    Simplification::Success()
      .input(clause({ ap(lam(srt, db0), {a}) != b }))
      .expected(clause({ a != b }))
    )

// Argument is duplicated: (\. g db0 db0) f(x,y)  ==>  g f(x,y) f(x,y)
TEST_SIMPLIFY(beta_duplicates_argument,
    Simplification::Success()
      .input(clause({ ap(lam(srt, ap(g, {db0, db0})), {f(x,y)}) != a }))
      .expected(clause({ ap(g, {f(x,y), f(x,y)}) != a }))
    )

// Over-application: (\. g db0) a b  ==>  g a b
TEST_SIMPLIFY(beta_over_application,
    Simplification::Success()
      .input(clause({ ap(lam(srt, ap(g, db0)), {a, b}) != c }))
      .expected(clause({ ap(g, {a, b}) != c }))
    )

// Under-application: (\.\. g db0 db1) a  ==>  \. g db0 a
TEST_SIMPLIFY(beta_under_application,
    Simplification::Success()
      .input(clause({ ap(lam(srt, lam(srt, ap(g, {db0, db1}))), {a}) != h1 }))
      .expected(clause({ lam(srt, ap(g, {db0, a})) != h1 }))
    )

// Redex in an argument position
TEST_SIMPLIFY(beta_redex_inside_argument,
    Simplification::Success()
      .input(clause({ ap(g, {ap(lam(srt, db0), {a}), b}) != c }))
      .expected(clause({ ap(g, {a, b}) != c }))
    )

// Redex in both sides of the equation, with a redex under a binder
TEST_SIMPLIFY(beta_both_sides,
    Simplification::Success()
      .input(clause({ ap(lam(srt, ap(g, db0)), {a}) != lam(srt, ap(lam(srt, ap(h, {db0, b})), {db0})) }))
      .expected(clause({ ap(g, a) != lam(srt, ap(h, {db0, b})) }))
    )

// Shifting: the substituted argument is a loose index that must be lifted
// under the binder it is moved beneath.
//   \. (\.\. g db0 db1) db0   ==>   \.\. g db0 db1
TEST_SIMPLIFY(beta_shifts_free_indices,
    Simplification::Success()
      .input(clause({ lam(srt, ap(lam(srt, lam(srt, ap(g, {db0, db1}))), {db0})) != h }))
      .expected(clause({ lam(srt, lam(srt, ap(g, {db0, db1}))) != h }))
    )

// Reduction happens in several literals of the same clause
TEST_SIMPLIFY(beta_multiple_literals,
    Simplification::Success()
      .input(clause({ ap(lam(srt, db0), {a}) != b,
                      ap(lam(srt, ap(g, db0)), {c}) == ap(g, a) }))
      .expected(clause({ a != b,
                         ap(g, c) == ap(g, a) }))
    )

/* ------------------------------------------------------------------ */
/*  Eta reduction                                                      */
/* ------------------------------------------------------------------ */

// \. g db0  ==>  g
TEST_SIMPLIFY(eta_simple,
    Simplification::Success()
      .input(clause({ lam(srt, ap(g, db0)) != h }))
      .expected(clause({ g != h }))
    )

// Partial application head: \. g a db0  ==>  g a
TEST_SIMPLIFY(eta_with_prefix_args,
    Simplification::Success()
      .input(clause({ lam(srt, ap(g, {a, db0})) != ap(h, b) }))
      .expected(clause({ ap(g, a) != ap(h, b) }))
    )

// Double eta: \.\. g db1 db0  ==>  g
TEST_SIMPLIFY(eta_double,
    Simplification::Success()
      .input(clause({ lam(srt, lam(srt, ap(g, {db1, db0}))) != h }))
      .expected(clause({ g != h }))
    )

// Eta redex under a binder that is not itself eta-reducible
//   \. g1 (\. g db0) db0   ==>   \. g1 g db0   ==>  h g
TEST_SIMPLIFY(eta_under_application,
    Simplification::Success()
      .input(clause({ lam(srt, ap(g1, {lam(srt, ap(g, db0)), db0})) != h1 }))
      .expected(clause({ ap(g1, g) != h1 }))
    )

// Eta in several literals
TEST_SIMPLIFY(eta_multiple_literals,
    Simplification::Success()
      .input(clause({ lam(srt, ap(g, db0)) != h,
                      lam(srt, ap(h, db0)) == g }))
      .expected(clause({ g != h,
                         h == g }))
    )

// Eta not applicable: the bound variable also occurs in the head's arguments
TEST_SIMPLIFY(eta_not_applicable_var_occurs_twice,
    Simplification::NotApplicable()
      .input(clause({ lam(srt, ap(g, {db0, db0})) != h1 }))
    )

// Eta not applicable: the bound variable is not the last argument
TEST_SIMPLIFY(eta_not_applicable_var_not_last,
    Simplification::NotApplicable()
      .input(clause({ lam(srt, ap(g, {db0, a})) != h1 }))
    )

// Eta not applicable: the bound variable is the head
TEST_SIMPLIFY(eta_not_applicable_var_is_head,
    Simplification::NotApplicable()
      .input(clause({ lam(srt, ap(db01, a)) != h1 }))
    )

/* ------------------------------------------------------------------ */
/*  Beta and eta interacting                                           */
/* ------------------------------------------------------------------ */

// Beta produces an eta redex: (\.\. db1 db0) g  ==>  \. g db0  ==>  g
TEST_SIMPLIFY(beta_then_eta,
    Simplification::Success()
      .input(clause({ ap(lam(arrow(srt, srt), lam(srt, ap(db11, db0))), {h1}) != h1 }))
      .expected(clause({ h1 != h1 }))
    )

// Beta under a binder produces an eta redex: \. (\. g db0) db0  ==>  \. g db0  ==>  g
TEST_SIMPLIFY(beta_under_lambda_then_eta,
    Simplification::Success()
      .input(clause({ lam(srt, ap(lam(srt, ap(g, db0)), {db0})) != h }))
      .expected(clause({ g != h }))
    )

// Applying the result of an eta-reducible lambda: (\. g db0) a  ==>  g a
TEST_SIMPLIFY(eta_redex_applied,
    Simplification::Success()
      .input(clause({ ap(lam(srt, ap(g, db0)), {a}) != ap(g, b) }))
      .expected(clause({ ap(g, a) != ap(g, b) }))
    )

/* ------------------------------------------------------------------ */
/*  Nothing to do                                                      */
/* ------------------------------------------------------------------ */

// Already in beta-eta normal form
TEST_SIMPLIFY(not_applicable_normal_form_1,
    Simplification::NotApplicable()
      .input(clause({ ap(g, {a, b}) != ap(g, {f(x,y), b}) }))
    )

// Lambda that is neither a redex nor eta-reducible
TEST_SIMPLIFY(not_applicable_normal_form_2,
    Simplification::NotApplicable()
      .input(clause({ lam(srt, ap(g, {db0, a})) != lam(srt, ap(h, {db0, db0})) }))
    )
