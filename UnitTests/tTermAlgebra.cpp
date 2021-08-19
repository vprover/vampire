/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Shell/TermAlgebra.hpp"

using namespace Shell;

TEST_FUN(excludeTermFromAvailables) {
  DECL_DEFAULT_VARS
  DECL_SORT(ts)
  DECL_SORT(nts)
  DECL_CONST(b1, ts)
  DECL_CONST(b2, ts)
  DECL_FUNC(r1, {nts, ts}, ts)
  DECL_FUNC(r2, {nts, ts}, ts)
  DECL_TERM_ALGEBRA(ts, {b1, b2, r1, r2})
  DECL_CONST(f, ts)

  auto ta = env.signature->getTermAlgebraOfSort(ts.sortId());
  ASS(ta);

  TermStack a = { b1(), b2(), r1(x0, x1), r2(x2, x3) };
  unsigned var = 4;

  ta->excludeTermFromAvailables(a, b2(), var);
  TermStack exp1 = { b1(), r1(x0, x1), r2(x2,x3) };
  ASS_EQ(a, exp1);

  ta->excludeTermFromAvailables(a, r2(x,b1()), var);
  TermStack exp2 = { b1(), r1(x0, x1), r2(x2,b2()), r2(x2,r1(x4,x5)), r2(x2,r2(x6,x7)) };
  ASS_EQ(a, exp2);

  // can't exclude non ctor or dtor terms
  ta->excludeTermFromAvailables(a, r1(x,f()), var);
  ASS_EQ(a, exp2);
}

TEST_FUN(excludeNested) {
  DECL_DEFAULT_VARS
  DECL_SORT(ts)
  DECL_SORT(nts)
  DECL_CONST(b, ts)
  DECL_FUNC(r, {nts, ts}, ts)
  DECL_TERM_ALGEBRA(ts, {b, r})

  auto ta = env.signature->getTermAlgebraOfSort(ts.sortId());
  ASS(ta);

  TermStack a = { x0 };
  unsigned var = 1;

  ta->excludeTermFromAvailables(a, r(x0,r(x1,r(x2,r(x3,x4)))), var);
  TermStack exp1 = { b(), r(x1,b()), r(x1,r(x3,b())), r(x1,r(x3,r(x5,b()))) };
  ASS_EQ(a, exp1);
}
