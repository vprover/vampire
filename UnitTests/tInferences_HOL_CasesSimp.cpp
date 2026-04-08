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
#include "Inferences/HOL/CasesSimp.hpp"

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
  DECL_CONST(a, Bool)                              \
  DECL_CONST(b, Bool)                              \
  DECL_CONST(c, srt)                               \
  DECL_CONST(f, arrow(Bool,srt))                   \
  DECL_CONST(p, arrow(srt,Bool))

#define MY_SIMPL_TESTER Simplification::SimplificationTester
#define MY_SIMPL_RULE   CasesSimp

TEST_SIMPLIFY_MANY(fail_1,
  Simplification::NotApplicableMany()
    .input(clause({ ap(andP, fols) == lam(Bool,troo) }))
  )

TEST_SIMPLIFY_MANY(fail_2,
  Simplification::NotApplicableMany()
    .input(clause({ a == b }))
  )

TEST_SIMPLIFY_MANY(success_1,
  Simplification::SuccessMany()
    .input(clause({ ap(f, ap(notP, a)) == c }))
    .expected({
      clause({ ap(f, ap(notP, troo)) == c, a == fols }),
      clause({ ap(f, ap(notP, fols)) == c, a == troo }),
      clause({ ap(f, troo) == c, ap(notP, a) == fols }),
      clause({ ap(f, fols) == c, ap(notP, a) == troo }),
    })
  )

TEST_SIMPLIFY_MANY(success_2,
  Simplification::SuccessMany()
    .input(clause({ ap(andP, b) != lam(Bool,a) }))
    .expected({
      clause({ ap(andP, troo) != lam(Bool,a), b == fols }),
      clause({ ap(andP, fols) != lam(Bool,a), b == troo })
    })
  )

TEST_SIMPLIFY_MANY(success_3,
  Simplification::SuccessMany()
    .input(clause({ ap(f, ap(p, x)) == y, ap(p, x) == a }))
    .expected({
      clause({ ap(f, troo) == y, ap(p, x) == a, ap(p, x) == fols }),
      clause({ ap(f, fols) == y, ap(p, x) == a, ap(p, x) == troo }),
    })
  )
