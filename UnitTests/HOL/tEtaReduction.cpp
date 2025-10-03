/*
* This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/HOL/HOL.hpp"
#include "Test/HOLUtils.hpp"
#include "Test/UnitTesting.hpp"

using namespace Test::HOL;
using HOL::convert::toNameless;

TEST_FUN(eta_reduction_1) {
  env.setHigherOrder(true);
  env.options->setTraceback(true);
  const auto& D = *Defs::instance();

  auto a = D.a;
  ASS_EQ(a, toNameless(a))
  ASS_EQ(HOL::reduce::etaNF(a), a)

  auto srt = TermList(AtomicSort::arrowSort(D.srt, D.srt));
  TypedTermList f = mkConst("f1", srt);
  TypedTermList x0 = {D.x0, D.srt};
  auto term = lam(x0, app({f, x0}));
  ASS_EQ(HOL::reduce::etaNF(toNameless(term)), f)

  srt = TermList(AtomicSort::arrowSort(D.srt, srt));
  f = mkConst("f2", srt);
  TypedTermList x1 = {D.x1, D.srt};
  term = lam(x0, app({f, x0, x1}));
  ASS_EQ(HOL::reduce::etaNF(toNameless(term)), f)
}