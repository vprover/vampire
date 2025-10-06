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
  auto term = toNameless(lam(x0, app({f, x0})));
  ASS_EQ(termListToString(term, Options::HPrinting::TPTP),
         "(^[Y0 : srt]: (f1 @ Y0))")
  ASS_EQ(termListToString(term, Options::HPrinting::RAW),
         "vLAM(srt,srt,vAPP(srt,srt,f1,db0(srt)))")
  ASS_EQ(HOL::reduce::etaNF(term), f)

  srt = TermList(AtomicSort::arrowSort(D.srt, srt));
  f = mkConst("f2", srt);
  TypedTermList x1 = {D.x1, D.srt};
  term = toNameless(lam({x0, x1}, app({f, x0, x1})));
  ASS_EQ(termListToString(term, Options::HPrinting::TPTP),
         "(^[Y0 : srt]: ((^[Y1 : srt]: (f2 @ Y0 @ Y1))))")
  ASS_EQ(termListToString(term, Options::HPrinting::RAW),
         "vLAM(srt,srt > srt,vLAM(srt,srt,vAPP(srt,srt,vAPP(srt,srt > srt,f2,db1(srt)),db0(srt))))")
  ASS_EQ(HOL::reduce::etaNF(term), f)

  srt = TermList(AtomicSort::arrowSort(D.srt, srt));
  f = mkConst("f3", srt);
  TypedTermList x2 = {TermList::var(2), D.srt};
  term = toNameless(lam({x0, x1, x2}, app({f, x0, x1, x2})));
  ASS_EQ(termListToString(term, Options::HPrinting::TPTP),
         "(^[Y0 : srt]: ((^[Y1 : srt]: ((^[Y2 : srt]: (f3 @ Y0 @ Y1 @ Y2))))))")
  ASS_EQ(termListToString(term, Options::HPrinting::RAW),
         "vLAM(srt,srt > (srt > srt),vLAM(srt,srt > srt,vLAM(srt,srt,vAPP(srt,srt,vAPP(srt,srt > srt,vAPP(srt,srt > (srt > srt),f3,db2(srt)),db1(srt)),db0(srt)))))")
  ASS_EQ(HOL::reduce::etaNF(term), f)
}