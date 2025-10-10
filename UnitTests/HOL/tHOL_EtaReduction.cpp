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
using HOL::reduce::etaNF;

HOL_TEST_FUN(eta_reduction_1) {
  ASS_EQ(D.a, toNameless(D.a))
  ASS_EQ(etaNF(D.a), D.a)

  auto term = toNameless(lam(x(0), app({D.f, x(0)})));
  ASS_EQ(termListToString(term, Options::HPrinting::TPTP),
         "(^[Y0 : srt]: (f @ Y0))")
  ASS_EQ(termListToString(term, Options::HPrinting::RAW),
         "vLAM(srt,srt,vAPP(srt,srt,f,db0(srt)))")
  ASS_EQ(etaNF(term), D.f)

  term = toNameless(lam({x(0), x(1)}, app({D.f2, x(0), x(1)})));
  ASS_EQ(termListToString(term, Options::HPrinting::TPTP),
         "(^[Y0 : srt]: ((^[Y1 : srt]: (f2 @ Y0 @ Y1))))")
  ASS_EQ(termListToString(term, Options::HPrinting::RAW),
         "vLAM(srt,srt > srt,vLAM(srt,srt,vAPP(srt,srt,vAPP(srt,srt > srt,f2,db1(srt)),db0(srt))))")
  ASS_EQ(etaNF(term), D.f2)

  term = toNameless(lam({x(0), x(1), x(2)}, app({D.f3, x(0), x(1), x(2)})));
  ASS_EQ(termListToString(term, Options::HPrinting::TPTP),
         "(^[Y0 : srt]: ((^[Y1 : srt]: ((^[Y2 : srt]: (f3 @ Y0 @ Y1 @ Y2))))))")
  ASS_EQ(termListToString(term, Options::HPrinting::RAW),
         "vLAM(srt,srt > (srt > srt),vLAM(srt,srt > srt,vLAM(srt,srt,vAPP(srt,srt,vAPP(srt,srt > srt,vAPP(srt,srt > (srt > srt),f3,db2(srt)),db1(srt)),db0(srt)))))")
  ASS_EQ(etaNF(term), D.f3)
}

HOL_TEST_FUN(eta_reduction_2) {
  auto term = toNameless(lam({x(0), x(1), x(2)}, app({D.f3, x(0), x(2), x(1)})));

  ASS_EQ(termListToString(term, Options::HPrinting::RAW),
         "vLAM(srt,srt > (srt > srt),vLAM(srt,srt > srt,vLAM(srt,srt,vAPP(srt,srt,vAPP(srt,srt > srt,vAPP(srt,srt > (srt > srt),f3,db2(srt)),db0(srt)),db1(srt)))))");
  ASS_EQ(etaNF(term), term)
}

HOL_TEST_FUN(eta_reduction_3) {
  auto v0 = x(0, AtomicSort::arrowSort({D.srt, D.srt, D.srt}));
  auto term = toNameless(lam({v0, x(1), x(2)}, app({v0, x(1), x(2)})));
  auto expected = toNameless(lam(v0, v0));

  ASS_EQ(expected, HOL::create::namelessLambda(v0.sort(), v0.sort(), HOL::getDeBruijnIndex(0, v0.sort())))
  ASS_EQ(etaNF(term), expected)
}

HOL_TEST_FUN(eta_reduction_4) {
  auto term = toNameless(lam(x(0), app({D.f2, x(0), x(0)})));

  ASS_EQ(etaNF(term), term)
}

HOL_TEST_FUN(eta_reduction_5) {
  auto v0 = x(0, D.fSrt);
  auto term = toNameless(lam(v0, app(D.g, lam(x(1), app(v0, x(1))))));

  ASS_EQ(etaNF(term), D.g)
}