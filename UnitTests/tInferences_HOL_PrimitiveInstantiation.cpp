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
#include "Inferences/HOL/PrimitiveInstantiation.hpp"

#include "Test/GenerationTester.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                            \
  DECL_SORT(srt)                                   \
  DECL_SORT_BOOL                                   \
  TROO                                             \
  FOLS                                             \
  DECL_NOT_PROXY                                   \
  DECL_EQ_PROXY(srt)                               \
  DECL_VAR_SORTED(xs, 0, arrow(srt, Bool))         \
  DECL_VAR_SORTED(ys, 1, arrow(srt, srt))          \
  DECL_VAR_SORTED(zs, 2, arrow(srt, Bool))         \
  DECL_VAR_SORTED(us, 3, arrow({srt, srt}, Bool))  \
  DECL_VAR_SORTED(vs, 4, arrow(Bool, Bool))        \
  DECL_VAR_SORTED(ws, 5, arrow({srt, srt}, Bool))  \
  DECL_CONST(f, arrow(srt, Bool))                  \
  DECL_CONST(f1, arrow(srt, Bool))                 \
  DECL_CONST(g, arrow(srt, srt))                   \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                \
  DECL_DE_BRUIJN_INDEX(db1, 1, srt)                \
  DECL_CONST(a, Bool)                              \
  DECL_CONST(b, srt)                               \
  DECL_CONST(c, srt)

#define MY_GEN_RULE   PrimitiveInstantiation
#define MY_GEN_TESTER Generation::GenerationTester

// not done for non-selected literals
TEST_GENERATION(fail_1,
    Generation::AsymmetricTest()
      .input( clause({ ap(f,b) == ap(xs,c) }))
      .expected(none())
    )

// not done for non-bool literals
TEST_GENERATION(fail_2,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(g,b) == ap(ys,c)) }))
      .expected(none())
    )

// not done for non-applied variables
TEST_GENERATION(fail_3,
    Generation::AsymmetricTest()
      .input( clause({ selected(f == xs) }))
      .expected(none())
    )

// not done for rigid-rigid literals
TEST_GENERATION(fail_4,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(f,b) == ap(f1,c)) }))
      .expected(none())
    )

// not done for rigid-rigid literals
TEST_GENERATION(fail_5,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(xs,b) == ap(xs,c)) }))
      .expected(none())
    )

TEST_GENERATION(success_1,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(f,c) == ap(xs,c)) }))
      .expected(exactly(
        clause({ ap(f,c) == ap(lam(srt,troo),c) }),
        clause({ ap(f,c) == ap(lam(srt,fols),c) }),
        clause({ ap(f,c) == ap(lam(srt,ap(notP,ap(zs,db0))),c) })
      ))
    )

TEST_GENERATION(success_2,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(f,c) == ap(ap(us,c),b)) }))
      .expected(exactly(
        clause({ ap(f,c) == ap(lam(srt, lam(srt, troo)), {c, b}) }),
        clause({ ap(f,c) == ap(lam(srt, lam(srt, fols)), {c, b}) }),
        clause({ ap(f,c) == ap(lam(srt, lam(srt, ap(notP, ap(ap(ws,db1),db0)))), {c, b}) }),
        clause({ ap(f,c) == ap(lam(srt, lam(srt, ap(eqP,{db1,db0}))), {c, b}) }),
        clause({ ap(f,c) == ap(lam(srt, lam(srt, ap(notP, ap(eqP,{db1,db0})))), {c, b}) })
      ))
    )
