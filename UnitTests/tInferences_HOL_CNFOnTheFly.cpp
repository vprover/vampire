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
#include "Inferences/CNFOnTheFly.hpp"

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
  DECL_CONST(a, Bool)                              \
  DECL_CONST(b, Bool)

#define MY_SIMPL_TESTER Simplification::SimplificationTester

// EagerClausificationISE

#define MY_SIMPL_RULE EagerClausificationISE

// equalities between Boolean terms

TEST_SIMPLIFY_MANY(eq_success_1,
    Simplification::SuccessMany()
      .input(clause({ a == b }))
      .expected({
        clause({ a == troo, b == fols }),
        clause({ a == fols, b == troo }),
      })
    )

TEST_SIMPLIFY_MANY(eq_success_2,
    Simplification::SuccessMany()
      .input(clause({ a != b }))
      .expected({
        clause({ a == troo, b == troo }),
        clause({ a == fols, b == fols }),
      })
    )

// negation

TEST_SIMPLIFY_MANY(neg_success_1,
    Simplification::SuccessMany()
      .input(clause({ ap(notP, a) == troo }))
      .expected({
        clause({ a == fols }),
      })
    )

TEST_SIMPLIFY_MANY(neg_success_2,
    Simplification::SuccessMany()
      .input(clause({ ap(notP, a) == fols }))
      .expected({
        clause({ a == troo }),
      })
    )

TEST_SIMPLIFY_MANY(neg_success_3,
    Simplification::SuccessMany()
      .input(clause({ ap(notP, a) != troo }))
      .expected({
        clause({ a == troo }),
      })
    )

TEST_SIMPLIFY_MANY(neg_success_4,
    Simplification::SuccessMany()
      .input(clause({ ap(notP, a) != fols }))
      .expected({
        clause({ a == fols }),
      })
    )

// conjunction

TEST_SIMPLIFY_MANY(conj_success_1,
    Simplification::SuccessMany()
      .input(clause({ ap(andP, {a, b}) == troo }))
      .expected({
        clause({ a == troo }),
        clause({ b == troo }),
      })
    )

TEST_SIMPLIFY_MANY(conj_success_2,
    Simplification::SuccessMany()
      .input(clause({ ap(andP, {a, b}) == fols }))
      .expected({
        clause({ a == fols, b == fols }),
      })
    )

TEST_SIMPLIFY_MANY(conj_success_3,
    Simplification::SuccessMany()
      .input(clause({ ap(andP, {a, b}) != troo }))
      .expected({
        clause({ a == fols, b == fols }),
      })
    )

TEST_SIMPLIFY_MANY(conj_success_4,
    Simplification::SuccessMany()
      .input(clause({ ap(andP, {a, b}) != fols }))
      .expected({
        clause({ a == troo }),
        clause({ b == troo }),
      })
    )

// disjunction

TEST_SIMPLIFY_MANY(disj_success_1,
    Simplification::SuccessMany()
      .input(clause({ ap(orP, {a, b}) == troo }))
      .expected({
        clause({ a == troo, b == troo }),
      })
    )

TEST_SIMPLIFY_MANY(disj_success_2,
    Simplification::SuccessMany()
      .input(clause({ ap(orP, {a, b}) == fols }))
      .expected({
        clause({ a == fols }),
        clause({ b == fols }),
      })
    )

TEST_SIMPLIFY_MANY(disj_success_3,
    Simplification::SuccessMany()
      .input(clause({ ap(orP, {a, b}) != troo }))
      .expected({
        clause({ a == fols }),
        clause({ b == fols }),
      })
    )

TEST_SIMPLIFY_MANY(disj_success_4,
    Simplification::SuccessMany()
      .input(clause({ ap(orP, {a, b}) != fols }))
      .expected({
        clause({ a == troo, b == troo }),
      })
    )

// implication

TEST_SIMPLIFY_MANY(imp_success_1,
    Simplification::SuccessMany()
      .input(clause({ ap(impP, {a, b}) == troo }))
      .expected({
        clause({ a == fols, b == troo }),
      })
    )

TEST_SIMPLIFY_MANY(imp_success_2,
    Simplification::SuccessMany()
      .input(clause({ ap(impP, {a, b}) == fols }))
      .expected({
        clause({ a == troo }),
        clause({ b == fols }),
      })
    )

TEST_SIMPLIFY_MANY(imp_success_3,
    Simplification::SuccessMany()
      .input(clause({ ap(impP, {a, b}) != troo }))
      .expected({
        clause({ a == troo }),
        clause({ b == fols }),
      })
    )

TEST_SIMPLIFY_MANY(imp_success_4,
    Simplification::SuccessMany()
      .input(clause({ ap(impP, {a, b}) != fols }))
      .expected({
        clause({ a == fols, b == troo }),
      })
    )

// equivalence

// TEST_SIMPLIFY_MANY(iff_success_1,
//     Simplification::SuccessMany()
//       .input(clause({ ap(iffP, {a, b}) == troo }))
//       .expected({
//         clause({ a == fols, b == troo }),
//         clause({ b == fols, a == troo }),
//       })
//     )

// TEST_SIMPLIFY_MANY(iff_success_2,
//     Simplification::SuccessMany()
//       .input(clause({ ap(impP, {a, b}) == fols }))
//       .expected({
//         clause({ a == troo, b == troo }),
//         clause({ a == fols, b == fols }),
//       })
//     )

// TEST_SIMPLIFY_MANY(iff_success_3,
//     Simplification::SuccessMany()
//       .input(clause({ ap(impP, {a, b}) != troo }))
//       .expected({
//         clause({ a == troo }),
//         clause({ b == fols }),
//       })
//     )

// TEST_SIMPLIFY_MANY(iff_success_4,
//     Simplification::SuccessMany()
//       .input(clause({ ap(impP, {a, b}) != fols }))
//       .expected({
//         clause({ a == fols, b == troo }),
//       })
//     )
