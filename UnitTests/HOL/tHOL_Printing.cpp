/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Shell/Options.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/HOLUtils.hpp"

#include <map>

constexpr auto RAW = Options::HPrinting::RAW;
constexpr auto DB_INDICES = Options::HPrinting::DB_INDICES;
constexpr auto PRETTY = Options::HPrinting::PRETTY;
constexpr auto TPTP = Options::HPrinting::TPTP;

using namespace Test::HOL;

void runTest(TermList term, const std::map<Options::HPrinting, std::string>& reps) {
  for (const auto& [printOpt, expected] : reps)
    ASS_EQ(termListToString(term, printOpt), expected)
}

HOL_TEST_FUN(hol_print_1) {
  const auto x0F = x(0, Defs::instance()->fSrt);
  const auto x1F = x(1, Defs::instance()->fSrt);

  runTest(
    lam({x0F, x(1)}, x(1)),
    { {RAW,        "(^[X0 : (srt > srt), X1 : srt] : (X1))"},
      {DB_INDICES, "(^[X0 : (srt > srt), X1 : srt] : (X1))"},
      {PRETTY,     "(λX0 : (srt → srt), X1 : srt : (X1))"},
      {TPTP,       "(^[X0 : (srt > srt), X1 : srt] : (X1))"} }
  );
  
  runTest(
    lam({x0F, x(1)}, app(x0F, x(1))),
    { {RAW,        "(^[X0 : (srt > srt), X1 : srt] : (vAPP(srt,srt,X0,X1)))"},
      {DB_INDICES, "(^[X0 : (srt > srt), X1 : srt] : ((X0 @ X1)))"},
      {PRETTY,     "(λX0 : (srt → srt), X1 : srt : ((X0 X1)))"},
      {TPTP,       "(^[X0 : (srt > srt), X1 : srt] : ((X0 @ X1)))"} }
  );

  runTest(
    app(D.f, x(1)),
    { {RAW,        "vAPP(srt,srt,f,X1)"},
      {DB_INDICES, "(f @ X1)"},
      {PRETTY,     "(f X1)"},
      {TPTP,       "(f @ X1)"} }
  );

  runTest(
    lam(x(1), app(D.f, x(1))),
    { {RAW,        "(^[X1 : srt] : (vAPP(srt,srt,f,X1)))"},
      {DB_INDICES, "(^[X1 : srt] : ((f @ X1)))"},
      {PRETTY,     "(λX1 : srt : ((f X1)))"},
      {TPTP,       "(^[X1 : srt] : ((f @ X1)))"} }
  );

  runTest(
    lam(x1F, lam(x(1), x(1))),
    { {RAW,        "(^[X1 : (srt > srt)] : ((^[X1 : srt] : (X1))))" }, 
      {DB_INDICES, "(^[X1 : (srt > srt)] : ((^[X1 : srt] : (X1))))" }, 
      {PRETTY,     "(λX1 : (srt → srt) : ((λX1 : srt : (X1))))" }, 
      {TPTP,       "(^[X1 : (srt > srt)] : ((^[X1 : srt] : (X1))))" } }
  );
}

HOL_TEST_FUN(hol_print_2) {
  using HOL::convert::toNameless;

  const auto x0F = x(0, Defs::instance()->fSrt);
  const auto x1F = x(1, Defs::instance()->fSrt);

  runTest(
    toNameless(lam({x0F, x(1)}, x(1))),
    { {RAW,        "vLAM(srt > srt,srt > srt,vLAM(srt,srt,db0(srt)))" },
      {DB_INDICES, "(^db0 : srt > srt. ((^db1 : srt. (db0_0))))" },
      {PRETTY,     "(λy0 : srt → srt. (λy1 : srt. y1))" },
      {TPTP,       "(^[Y0 : srt > srt]: ((^[Y1 : srt]: (Y1))))" } }
  );

  runTest(
    toNameless(lam({x0F, x(1)}, app(x0F, x(1)))),
    { {RAW,        "vLAM(srt > srt,srt > srt,vLAM(srt,srt,vAPP(srt,srt,db1(srt > srt),db0(srt))))" },
      {DB_INDICES, "(^db0 : srt > srt. ((^db1 : srt. (db1_1 @ db0_0))))" },
      {PRETTY,     "(λy0 : srt → srt. (λy1 : srt. (y0 y1)))" },
      {TPTP,       "(^[Y0 : srt > srt]: ((^[Y1 : srt]: (Y0 @ Y1))))" } }
  );

  runTest(
    toNameless(app(D.f, x(1))),
    { {RAW,        "vAPP(srt,srt,f,X1)"},
      {DB_INDICES, "(f @ X1)"},
      {PRETTY,     "(f X1)"},
      {TPTP,       "(f @ X1)"} }
  );

  runTest(
    toNameless(lam(x(1), app(D.f, x(1)))),
    { {RAW,        "vLAM(srt,srt,vAPP(srt,srt,f,db0(srt)))"},
      {DB_INDICES, "(^db0 : srt. (f @ db0_0))"},
      {PRETTY,     "(λy0 : srt. (f y0))"},
      {TPTP,       "(^[Y0 : srt]: (f @ Y0))"} }
  );

  runTest(
    toNameless(lam(x1F, lam(x(1), x(1)))),
    { {RAW,        "vLAM(srt > srt,srt > srt,vLAM(srt,srt,db0(srt)))" },
      {DB_INDICES, "(^db0 : srt > srt. ((^db1 : srt. (db0_0))))" },
      {PRETTY,     "(λy0 : srt → srt. (λy1 : srt. y1))" },
      {TPTP,       "(^[Y0 : srt > srt]: ((^[Y1 : srt]: (Y1))))" }}
  );
}

HOL_TEST_FUN(hol_print_3) {
  runTest(
    D.f3.sort(),
    { {RAW,    "(srt > (srt > (srt > srt)))" },
      {PRETTY, "(srt → srt → srt → srt)" },
      {TPTP,   "(srt > srt > srt > srt)"} }
  );

  runTest(
    D.g.sort(),
    { {RAW,    "((srt > srt) > srt)" },
      {PRETTY, "((srt → srt) → srt)" },
      {TPTP,   "((srt > srt) > srt)"} }
  );

  runTest(
    D.h.sort(),
    { {RAW,    "((srt > srt) > (srt > srt))" },
      {PRETTY, "((srt → srt) → srt → srt)" },
      {TPTP,   "((srt > srt) > srt > srt)"} }
  );
}