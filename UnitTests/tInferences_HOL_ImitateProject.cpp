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
#include "Test/GenerationTester.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Inferences/HOL/ImitateProject.hpp"

using namespace Test;

#define MY_SYNTAX_SUGAR                     \
  DECL_SORT(srt)                            \
  __ALLOW_UNUSED(                           \
    auto s2 = arrow(srt, srt);              \
    auto s3 = arrow({srt, srt}, srt);       \
  )                                         \
  DECL_DEFAULT_VARS                         \
  DECL_CONST(a, srt)                        \
  DECL_CONST(b, srt)                        \
  DECL_CONST(g, s3)                         \
  DECL_CONST(f, s2)                         \
  DECL_DE_BRUIJN_INDEX(db0, 0, srt)         \
  DECL_DE_BRUIJN_INDEX(db1, 1, srt)

#define MY_GEN_RULE   ImitateProject
#define MY_GEN_TESTER Generation::GenerationTester

TEST_GENERATION(test_01,
  Generation::AsymmetricTest()
    .input(clause({  selected(a != ap(x.sort(s2), a))  }))
    .expected(exactly(
      clause({  a != ap(lam(srt,db0), a)  }),
      clause({  a != ap(lam(srt,a), a)  })
    ))
  )

TEST_GENERATION(test_02,
  Generation::AsymmetricTest()
    .input(clause({  selected(ap(f, y) != ap(x.sort(s2), a))  }))
    .expected(exactly(
      clause({ ap(f, y) != ap(lam(srt, ap(f, ap(z.sort(s2), db0))), a)  })
    ))
  )

TEST_GENERATION(test_03,
  Generation::AsymmetricTest()
    .input(clause({  selected(ap(g, {a, b}) != ap(ap(x.sort(s3), b), a))  }))
    .expected(exactly(
      clause({ ap(g, {a, b}) != ap(lam(srt, lam(srt, ap(g, { ap(ap(y.sort(s3), db1), db0), ap(ap(z.sort(s3), db1), db0) }))), {b, a})  })
    ))
  )
