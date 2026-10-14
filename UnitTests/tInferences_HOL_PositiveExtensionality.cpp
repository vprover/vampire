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
#include "Inferences/HOL/PositiveExtensionality.hpp"

#include "Test/GenerationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_SORT(srt)                                   \
  DECL_VAR_SORTED(x, 0, srt)                       \
  DECL_VAR_SORTED(y, 1, srt)                       \
  DECL_VAR_SORTED(z, 2, srt)                       \
  DECL_CONST(f, arrow({srt, srt}, srt))            \
  DECL_CONST(g, arrow(srt, srt))                   \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)

#define MY_GEN_RULE   PositiveExtensionality
#define MY_GEN_TESTER Generation::GenerationTester

// not done for non-selected literals
TEST_GENERATION(fail_1,
    Generation::AsymmetricTest()
      .input( clause({ selected(x == y), ap(g,z) == ap(lam(srt, ap(f, {db0, x})),z) }))
      .expected(none())
    )

// not done for negative literals
TEST_GENERATION(fail_2,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(g,z) != ap(lam(srt, ap(f, {db0, x})),z)) }))
      .expected(none())
    )

// not done for functions with different applied vars
TEST_GENERATION(fail_3,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(g,x) == ap(lam(srt, ap(f, {db0, x})),y)), ap(f, {z, z}) == z }))
      .expected(none())
    )

// not done for functions with applied vars that occur in other parts of the literal
TEST_GENERATION(fail_4,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(g,x) == ap(lam(srt, ap(f, {db0, x})),x)), ap(f, {z, z}) == z }))
      .expected(none())
    )

// not done for functions with applied vars that occur in other parts of the clause
TEST_GENERATION(fail_5,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(g,y) == ap(lam(srt, ap(f, {db0, x})),y)), ap(f, {y, z}) == z }))
      .expected(none())
    )

TEST_GENERATION(success_1,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(g,y) == ap(lam(srt, ap(f, {db0, x})),y)), ap(f, {x, z}) == x }))
      .expected(exactly( clause({ g == lam(srt, ap(f, {db0, x})), ap(f, {x, z}) == x })))
    )
