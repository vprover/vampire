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
  DECL_DEFAULT_VARS                                \
  DECL_VAR(u, 3)                                   \
  DECL_VAR(v, 4)                                   \
  TROO                                             \
  FOLS                                             \
  DECL_NOT_PROXY                                   \
  DECL_AND_PROXY                                   \
  DECL_OR_PROXY                                    \
  DECL_EQ_PROXY(eqP)                               \
  DECL_PI_PROXY(piP)                               \
  DECL_SIGMA_PROXY(sgP)                            \
  DECL_VAR_SORTED(xs, 0, arrow(srt, Bool))         \
  DECL_VAR_SORTED(ys, 1, arrow(srt, srt))          \
  DECL_VAR_SORTED(zs, 2, arrow(srt, Bool))         \
  DECL_VAR_SORTED(zs2, 3, arrow(srt, Bool))        \
  DECL_VAR_SORTED(us, 3, arrow({srt, srt}, Bool))  \
  DECL_VAR_SORTED(vs, 4, arrow(Bool, Bool))        \
  DECL_VAR_SORTED(ws, 5, arrow({srt, srt}, Bool))  \
  DECL_VAR_SORTED(ws2, 5, arrow(Bool, Bool))       \
  DECL_CONST(f, arrow(srt, Bool))                  \
  DECL_CONST(f1, arrow({srt, srt}, Bool))          \
  DECL_CONST(g, arrow(srt, srt))                   \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)                \
  DECL_DE_BRUIJN_INDEX(db0B, 0, Bool)              \
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
      .input( clause({ selected(f == x) }))
      .expected(none())
    )

// not done for rigid-rigid literals
TEST_GENERATION(fail_4,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(f,b) == ap(f1, {c,x})) }))
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
        clause({ ap(f,c) == ap(lam(srt, lam(srt, ap(eqP(srt),{db1,db0}))), {c, b}) }),
        clause({ ap(f,c) == ap(lam(srt, lam(srt, ap(notP, ap(eqP(srt),{db1,db0})))), {c, b}) })
      ))
    )

TEST_GENERATION(success_3,
    Generation::AsymmetricTest()
      .input( clause({ selected(a != ap(vs,a)) }))
      .expected(exactly(
        clause({ a != ap(lam(Bool,db0B),a) }),
        clause({ a != ap(lam(Bool,troo),a) }),
        clause({ a != ap(lam(Bool,fols),a) }),
        clause({ a != ap(lam(Bool,ap(notP,ap(ws2,db0B))),a) })
      ))
    )

TEST_GENERATION(success_4,
    Generation::AsymmetricTest()
      .input( clause({ selected(a == ap(xs,c)) }))
      .options({ { "prim_inst_set", "and" } })
      .expected(exactly(
        clause({ a == ap(lam(srt,troo),c) }),
        clause({ a == ap(lam(srt,fols),c) }),
        clause({ a == ap(lam(srt,ap(andP, {ap(zs2,db0), ap(zs,db0)})),c) })
      ))
    )

TEST_GENERATION(success_5,
    Generation::AsymmetricTest()
      .input( clause({ selected(a == ap(xs,c)) }))
      .options({ { "prim_inst_set", "or" } })
      .expected(exactly(
        clause({ a == ap(lam(srt,troo),c) }),
        clause({ a == ap(lam(srt,fols),c) }),
        clause({ a == ap(lam(srt,ap(orP, {ap(zs2,db0), ap(zs,db0)})),c) })
      ))
    )

TEST_GENERATION(success_6,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(f1, {x,y}) == ap(arrow(srt,Bool),z,c)) }))
      .options({ { "prim_inst_set", "pi_sigma" } })
      .expected(exactly(
        clause({ ap(f1, {x,y}) == ap(lam(srt,troo),c) }),
        clause({ ap(f1, {x,y}) == ap(lam(srt,fols),c) }),
        clause({ ap(f1, {x,y}) == ap(lam(srt,ap(piP(z), ap(arrow({srt,z},Bool),u,db0))),c) }),
        clause({ ap(f1, {x,y}) == ap(lam(srt,ap(sgP(z), ap(arrow({srt,z},Bool),u,db0))),c) })
      ))
    )

TEST_GENERATION(success_7,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(f1, {x,z}) == ap(arrow(srt,Bool),y,c)) }))
      .options({ { "prim_inst_set", "equals" } })
      .expected(exactly(
        clause({ ap(f1, {x,z}) == ap(lam(srt,troo),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt,fols),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt,ap(eqP(y), { ap(arrow(srt,y),u,db0), ap(arrow(srt,y),v,db0) })),c) })
      ))
    )

TEST_GENERATION(success_8,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(f1, {x,z}) == ap(arrow(srt,Bool),y,c)) }))
      .options({ { "prim_inst_set", "small_set" } })
      .expected(exactly(
        clause({ ap(f1, {x,z}) == ap(lam(srt,troo),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt,fols),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt,ap(eqP(y), { ap(arrow(srt,y),u,db0), ap(arrow(srt,y),v,db0) })),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt,ap(notP, ap(arrow(srt,Bool),u,db0))),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt, ap(notP, ap(eqP(y), { ap(arrow(srt,y),u,db0), ap(arrow(srt,y),v,db0) }))),c) })
      ))
    )

TEST_GENERATION(success_9,
    Generation::AsymmetricTest()
      .input( clause({ selected(ap(f1, {x,z}) == ap(arrow(srt,Bool),y,c)) }))
      .options({ { "prim_inst_set", "all" } })
      .expected(exactly(
        clause({ ap(f1, {x,z}) == ap(lam(srt,troo),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt,fols),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt,ap(eqP(y), { ap(arrow(srt,y),u,db0), ap(arrow(srt,y),v,db0) })),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt,ap(notP, ap(arrow(srt,Bool),u,db0))),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt, ap(notP, ap(eqP(y), { ap(arrow(srt,y),u,db0), ap(arrow(srt,y),v,db0) }))),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt,ap(piP(y), ap(arrow({srt,y},Bool),u,db0))),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt,ap(sgP(y), ap(arrow({srt,y},Bool),u,db0))),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt,ap(andP, {ap(arrow(srt,Bool),u,db0), ap(arrow(srt,Bool),v,db0)})),c) }),
        clause({ ap(f1, {x,z}) == ap(lam(srt,ap(orP, {ap(arrow(srt,Bool),u,db0), ap(arrow(srt,Bool),v,db0)})),c) })
      ))
    )
