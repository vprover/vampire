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
#include "Inferences/HOL/NegativeExtensionality.hpp"

#include "Test/GenerationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_SORT(srt)                                   \
  DECL_VAR_SORTED(x, 0, srt)                       \
  DECL_VAR_SORTED(y, 1, srt)                       \
  DECL_VAR_SORTED(z, 2, srt)                       \
  DECL_VAR_SORTED(xs, 3, arrow({ srt, srt }, srt)) \
  DECL_VAR_SORTED(ys, 4, arrow(srt, srt))          \
  DECL_VAR_SORTED(zs, 5, arrow(srt, srt))          \
  DECL_PRED(p, { srt })                            \
  DECL_CONST(f, arrow({srt, srt}, srt))            \
  DECL_CONST(g, arrow(srt, srt))                   \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                \
  DECL_CONST(a, srt)                               \
  DECL_CONST(b, srt)

REGISTER_GEN_TESTER(Test::Generation::GenerationTester<NegativeExtensionality>(NegativeExtensionality()))

// not done for non-selected literals
TEST_GENERATION(fail_1,
    Generation::AsymmetricTest()
      .input( clause({ selected(x == y), g != lam(srt, ap(ap(f, db0), db0)) }))
      .expected(none())
    )

// not done for positive literals
TEST_GENERATION(fail_2,
    Generation::AsymmetricTest()
      .input( clause({ selected(g == lam(srt, ap(ap(f, db0), db0))) }))
      .expected(none())
    )

// not done for functions already applied
TEST_GENERATION(fail_3,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(g, x) == ap(lam(srt, ap(ap(f, db0), db0)), y)), x == y }))
      .expected(none())
    )

// not done for functions already applied
TEST_GENERATION(fail_4,
    Generation::AsymmetricTest()
      .input( clause({ selected(a != b) }))
      .expected(none())
    )

// TODO find a way to test with Skolems
// TEST_GENERATION(success_1,
//     Generation::AsymmetricTest()
//       .input( clause({ selected(g != lam(srt, ap(ap(f, x), x))) }))
//       .expected(exactly(clause({ ap(g, sk0()) != ap(lam(srt, ap(ap(f, x), x)), sk0()) })))
//     )

// TEST_GENERATION(success_2,
//     Generation::AsymmetricTest()
//       .input( clause({ selected(g != lam(srt, ap(ap(f, db0), db0))), x == y }))
//       .expected(exactly(clause({ ap(g, sk0()) != ap(lam(srt, ap(ap(f, db0), db0)), sk0()), x == y })))
//     )
