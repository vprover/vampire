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
#include "Inferences/HOL/CNFOnTheFly.hpp"

#include "Test/SimplificationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_LAM                                         \
  DECL_APP                                         \
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
  DECL_XOR_PROXY                                   \
  DECL_EQ_PROXY                                    \
  DECL_PI_PROXY                                    \
  DECL_SIGMA_PROXY                                 \
  DECL_CONST(a, Bool)                              \
  DECL_CONST(b, Bool)                              \
  DECL_CONST(c, srt)                               \
  DECL_CONST(d, srt)                               \
  DECL_CONST(f, arrow(srt,srt))                    \
  DECL_CONST(g, arrow(Bool,srt))                   \
  DECL_CONST(p, arrow(srt,Bool))                   \
  NEXT_INTRODUCED_FUN(sk0, 0)

#define MY_SIMPL_TESTER Simplification::SimplificationTester

// EagerClausificationISE

#define MY_SIMPL_RULE EagerClausificationISE

TEST_SIMPLIFY_MANY(fail_1,
    Simplification::NotApplicableMany()
      .input(clause({ ap(andP, a) == lam(Bool,troo) }))
    )

TEST_SIMPLIFY_MANY(fail_2,
    Simplification::NotApplicableMany()
      .input(clause({ ap(orP, b) != lam(Bool, fols) }))
    )

TEST_SIMPLIFY_MANY(fail_3,
    Simplification::NotApplicableMany()
      .input(clause({ lam(Bool, lam(Bool, ap(andP, {db(0, Bool), db(1, Bool)}))) == orP }))
    )

TEST_SIMPLIFY_MANY(fail_4,
    Simplification::NotApplicableMany()
      .input(clause({ ap(g, ap(andP, {a, b})) != c }))
    )

// equalities between Boolean terms

TEST_SIMPLIFY_MANY(eq_success_1,
    Simplification::SuccessMany()
      .input(clause({ c != d, a == b }))
      .expected({
        clause({ c != d, a == troo, b == fols }),
        clause({ c != d, a == fols, b == troo }),
      })
    )

TEST_SIMPLIFY_MANY(eq_success_2,
    Simplification::SuccessMany()
      .input(clause({ c != d, a != b }))
      .expected({
        clause({ c != d, a == troo, b == troo }),
        clause({ c != d, a == fols, b == fols }),
      })
    )

// negation

TEST_SIMPLIFY_MANY(neg_success_1,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(notP, a) == troo }))
      .expected({
        clause({ c != d, a == fols }),
      })
    )

TEST_SIMPLIFY_MANY(neg_success_2,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(notP, a) == fols }))
      .expected({
        clause({ c != d, a == troo }),
      })
    )

TEST_SIMPLIFY_MANY(neg_success_3,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(notP, a) != troo }))
      .expected({
        clause({ c != d, a == troo }),
      })
    )

TEST_SIMPLIFY_MANY(neg_success_4,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(notP, a) != fols }))
      .expected({
        clause({ c != d, a == fols }),
      })
    )

// conjunction

TEST_SIMPLIFY_MANY(conj_success_1,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(andP, {a, b}) == troo }))
      .expected({
        clause({ c != d, a == troo }),
        clause({ c != d, b == troo }),
      })
    )

TEST_SIMPLIFY_MANY(conj_success_2,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(andP, {a, b}) == fols }))
      .expected({
        clause({ c != d, a == fols, b == fols }),
      })
    )

TEST_SIMPLIFY_MANY(conj_success_3,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(andP, {a, b}) != troo }))
      .expected({
        clause({ c != d, a == fols, b == fols }),
      })
    )

TEST_SIMPLIFY_MANY(conj_success_4,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(andP, {a, b}) != fols }))
      .expected({
        clause({ c != d, a == troo }),
        clause({ c != d, b == troo }),
      })
    )

// disjunction

TEST_SIMPLIFY_MANY(disj_success_1,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(orP, {a, b}) == troo }))
      .expected({
        clause({ c != d, a == troo, b == troo }),
      })
    )

TEST_SIMPLIFY_MANY(disj_success_2,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(orP, {a, b}) == fols }))
      .expected({
        clause({ c != d, a == fols }),
        clause({ c != d, b == fols }),
      })
    )

TEST_SIMPLIFY_MANY(disj_success_3,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(orP, {a, b}) != troo }))
      .expected({
        clause({ c != d, a == fols }),
        clause({ c != d, b == fols }),
      })
    )

TEST_SIMPLIFY_MANY(disj_success_4,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(orP, {a, b}) != fols }))
      .expected({
        clause({ c != d, a == troo, b == troo }),
      })
    )

// implication

TEST_SIMPLIFY_MANY(imp_success_1,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(impP, {a, b}) == troo }))
      .expected({
        clause({ c != d, a == fols, b == troo }),
      })
    )

TEST_SIMPLIFY_MANY(imp_success_2,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(impP, {a, b}) == fols }))
      .expected({
        clause({ c != d, a == troo }),
        clause({ c != d, b == fols }),
      })
    )

TEST_SIMPLIFY_MANY(imp_success_3,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(impP, {a, b}) != troo }))
      .expected({
        clause({ c != d, a == troo }),
        clause({ c != d, b == fols }),
      })
    )

TEST_SIMPLIFY_MANY(imp_success_4,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(impP, {a, b}) != fols }))
      .expected({
        clause({ c != d, a == fols, b == troo }),
      })
    )

// equality

TEST_SIMPLIFY_MANY(equality_success_1,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(eqP(srt), {ap(f, c), d}) == troo }))
      .expected({
        clause({ c != d, ap(f, c) == d }),
      })
    )

TEST_SIMPLIFY_MANY(equality_success_2,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(eqP(srt), {ap(f, c), d}) != troo }))
      .expected({
        clause({ c != d, ap(f, c) != d }),
      })
    )

TEST_SIMPLIFY_MANY(equality_success_3,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(eqP(srt), {ap(f, c), d}) == fols }))
      .expected({
        clause({ c != d, ap(f, c) != d }),
      })
    )

TEST_SIMPLIFY_MANY(equality_success_4,
    Simplification::SuccessMany()
      .input(clause({ c != d, ap(eqP(srt), {ap(f, c), d}) != fols }))
      .expected({
        clause({ c != d, ap(f, c) == d }),
      })
    )

// pi

TEST_SIMPLIFY_MANY(pi_success_1,
    Simplification::SuccessMany()
      .input(clause({ ap(piP(srt), p) == troo }))
      .expected({
        clause({ ap(p, y) == troo }),
      })
    )

TEST_SIMPLIFY_MANY(pi_success_2,
    Simplification::SuccessMany()
      .input(clause({ ap(piP(srt), p) != fols }))
      .expected({
        clause({ ap(p, y) == troo }),
      })
    )

TEST_SIMPLIFY_MANY(pi_success_3,
    Simplification::SuccessMany()
      .input(clause({ ap(piP(srt), p) != troo }))
      .EXPECTED(exactly(clause({ ap(p, sk0()) == fols })))
    )

TEST_SIMPLIFY_MANY(pi_success_4,
    Simplification::SuccessMany()
      .input(clause({ ap(piP(srt), p) == fols }))
      .EXPECTED(exactly(clause({ ap(p, sk0()) == fols })))
    )

// sigma

TEST_SIMPLIFY_MANY(sigma_success_1,
    Simplification::SuccessMany()
      .input(clause({ ap(sigmaP(srt), p) == troo }))
      .EXPECTED(exactly(clause({ ap(p, sk0()) == troo })))
    )

TEST_SIMPLIFY_MANY(sigma_success_2,
    Simplification::SuccessMany()
      .input(clause({ ap(sigmaP(srt), p) != fols }))
      .EXPECTED(exactly(clause({ ap(p, sk0()) == troo })))
    )

TEST_SIMPLIFY_MANY(sigma_success_3,
    Simplification::SuccessMany()
      .input(clause({ ap(sigmaP(srt), p) != troo }))
      .expected({
        clause({ ap(p, y) == fols }),
      })
    )

TEST_SIMPLIFY_MANY(sigma_success_4,
    Simplification::SuccessMany()
      .input(clause({ ap(sigmaP(srt), p) == fols }))
      .expected({
        clause({ ap(p, y) == fols }),
      })
    )

// equivalence

TEST_SIMPLIFY_MANY(iff_not_applicable,
    Simplification::NotApplicableMany()
      .input(clause({ ap(iffP, {a, b}) == troo }))
    )

#undef  MY_SIMPL_RULE
#define MY_SIMPL_RULE IFFXORRewriterISE

TEST_SIMPLIFY_MANY(iffxor_fail_1,
    Simplification::NotApplicable()
      .input(clause({ ap(iffP, a) == lam(Bool,troo) }))
    )

TEST_SIMPLIFY_MANY(iffxor_fail_2,
    Simplification::NotApplicable()
      .input(clause({ ap(xorP, b) != lam(Bool, fols) }))
    )

TEST_SIMPLIFY_MANY(iffxor_fail_3,
    Simplification::NotApplicable()
      .input(clause({ ap(g, ap(xorP, {a, b})) != ap(g, ap(iffP, {b, a})) }))
    )

// equivalence

TEST_SIMPLIFY_MANY(iff_success_1,
    Simplification::Success()
      .input(clause({ ap(iffP, {a, b}) == troo }))
      .expected({
        clause({ a == b }),
      })
    )

TEST_SIMPLIFY_MANY(iff_success_2,
    Simplification::Success()
      .input(clause({ ap(iffP, {a, b}) != troo }))
      .expected({
        clause({ a != b }),
      })
    )

TEST_SIMPLIFY_MANY(iff_success_3,
    Simplification::Success()
      .input(clause({ ap(iffP, {a, b}) == fols }))
      .expected({
        clause({ a != b }),
      })
    )

TEST_SIMPLIFY_MANY(iff_success_4,
    Simplification::Success()
      .input(clause({ ap(iffP, {a, b}) != fols }))
      .expected({
        clause({ a == b }),
      })
    )

TEST_SIMPLIFY_MANY(xor_success_1,
    Simplification::Success()
      .input(clause({ ap(xorP, {a, b}) == troo }))
      .expected({
        clause({ a != b }),
      })
    )

TEST_SIMPLIFY_MANY(xor_success_2,
    Simplification::Success()
      .input(clause({ ap(xorP, {a, b}) != troo }))
      .expected({
        clause({ a == b }),
      })
    )

TEST_SIMPLIFY_MANY(xor_success_3,
    Simplification::Success()
      .input(clause({ ap(xorP, {a, b}) == fols }))
      .expected({
        clause({ a == b }),
      })
    )

TEST_SIMPLIFY_MANY(xor_success_4,
    Simplification::Success()
      .input(clause({ ap(xorP, {a, b}) != fols }))
      .expected({
        clause({ a != b }),
      })
    )
