/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Test/GenerationTester.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Inferences/Cases.hpp"

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

#define MY_GEN_TESTER Generation::GenerationTester
#define MY_GEN_RULE   Cases

// not performed for partially applied Boolean functions
TEST_GENERATION(fail_1,
  Generation::AsymmetricTest()
    .input(clause({ selected(ap(andP, fols) == lam(Bool,troo)) }))
    .expected(none())
  )

// not performed for top-level Booleans
TEST_GENERATION(fail_2,
  Generation::AsymmetricTest()
    .input(clause({ selected(a == b) }))
    .expected(none())
  )

// not performed for non-selected literals
TEST_GENERATION(fail_3,
  Generation::AsymmetricTest()
    .input(clause({ ap(f, ap(notP, a)) == c }))
    .expected(none())
  )

TEST_GENERATION(success_1,
  Generation::AsymmetricTest()
    .input(clause({ selected(ap(f, ap(notP, a)) == c) }))
    .expected({
      clause({ ap(f, ap(notP, troo)) == c, a == fols }),
      clause({ ap(f, troo) == c, ap(notP, a) == fols }),
    })
  )

TEST_GENERATION(success_2,
  Generation::AsymmetricTest()
    .input(clause({ selected(ap(andP, b) != lam(Bool,a)) }))
    .expected({
      clause({ ap(andP, troo) != lam(Bool,a), b == fols }),
    })
  )

TEST_GENERATION(success_4,
  Generation::AsymmetricTest()
    .input(clause({ selected(ap(f, ap(p, x)) == y), ap(p, x) != a }))
    .expected({
      clause({ ap(f, troo) == y, ap(p, x) != a, ap(p, x) == fols }),
    })
  )

TEST_GENERATION(success_3,
  Generation::AsymmetricTest()
    .input(clause({ selected(ap(f, ap(p, x)) == y), selected(ap(p, x) == a) }))
    .expected({
      clause({ ap(f, troo) == y, ap(p, x) == a, ap(p, x) == fols }),
    })
  )
