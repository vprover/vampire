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
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"

#include <list>
#include <map>

TermList mkAtomicSort(const std::string& name) {
  return TermList(AtomicSort::createConstant(name));
}

TermList mkConst(const std::string& name, TermList sort) {
  unsigned nameIndex = env.signature->addFunction(name, 0);
  env.signature->getFunction(nameIndex)->setType(OperatorType::getFunctionType({}, sort));
  return TermList(Term::createConstant(nameIndex));
}

constexpr Options::HPrinting RAW = Options::HPrinting::RAW;
constexpr Options::HPrinting DB_INDICES = Options::HPrinting::DB_INDICES;
constexpr Options::HPrinting PRETTY = Options::HPrinting::PRETTY;
constexpr Options::HPrinting TPTP = Options::HPrinting::TPTP;

#define LAM(...) TermList(HOL::create::lambda(__VA_ARGS__))
#define APP(...) HOL::create::app(__VA_ARGS__)

void runTest(const TermList& term, const std::map<Options::HPrinting, std::string>& reps) {
  for (const auto& [printOpt, expected] : reps) {
    env.options->setHolPrinting(printOpt);
    ASS_EQ(term.toString(), expected)
  }
}

class Defs {
  static Defs* _instance;

  Defs() {
    srt = mkAtomicSort("srt");
    fSrt = TermList(AtomicSort::arrowSort(srt, srt));
    x0 = TermList::var(0);
    x1 = TermList::var(1);
    f = mkConst("f", fSrt);
  }

public:
  static Defs* instance();
  TermList srt, fSrt, x0, x1, f;
};

Defs* Defs::_instance = nullptr;

Defs* Defs::instance()
{
  if (_instance == nullptr) {
    _instance = new Defs();
  }
  return _instance;
}

TEST_FUN(hol_print_1) {
  env.setHigherOrder(true);

  auto srt = Defs::instance()->srt;
  auto fSrt = Defs::instance()->fSrt;
  auto x0 = Defs::instance()->x0;
  auto x1 = Defs::instance()->x1;
  auto f = Defs::instance()->f;

  runTest(
    LAM({x0.var(), x1.var()}, {fSrt, srt}, {x1, srt}),
    { {RAW,        "(^[X0 : (srt > srt), X1 : srt] : (X1))"},
      {DB_INDICES, "(^[X0 : (srt > srt), X1 : srt] : (X1))"},
      {PRETTY,     "(λX0 : (srt → srt), X1 : srt : (X1))"},
      {TPTP,       "(^[X0 : (srt > srt), X1 : srt] : (X1))"} }
  );
  
  runTest(
    LAM({x0.var(), x1.var()}, {fSrt, srt}, {APP(fSrt, x0, x1), srt}),
    { {RAW,        "(^[X0 : (srt > srt), X1 : srt] : (vAPP(srt,srt,X0,X1)))"},
      {DB_INDICES, "(^[X0 : (srt > srt), X1 : srt] : ((X0 @ X1)))"},
      {PRETTY,     "(λX0 : (srt → srt), X1 : srt : ((X0 X1)))"},
      {TPTP,       "(^[X0 : (srt > srt), X1 : srt] : ((X0 @ X1)))"} }
  );

  runTest(
    APP(f, x1),
    { {RAW,        "vAPP(srt,srt,f,X1)"},
      {DB_INDICES, "(f @ X1)"},
      {PRETTY,     "(f X1)"},
      {TPTP,       "(f @ X1)"} }
  );

  runTest(
    LAM({x1.var()}, {srt}, {APP(f, x1), srt}),
    { {RAW,        "(^[X1 : srt] : (vAPP(srt,srt,f,X1)))"},
      {DB_INDICES, "(^[X1 : srt] : ((f @ X1)))"},
      {PRETTY,     "(λX1 : srt : ((f X1)))"},
      {TPTP,       "(^[X1 : srt] : ((f @ X1)))"} }
  );

  runTest(
    LAM({x1.var()}, {fSrt}, {LAM({x1.var()}, {srt}, {x1, srt}), fSrt}),
    { {RAW,        "(^[X1 : (srt > srt)] : ((^[X1 : srt] : (X1))))" }, 
      {DB_INDICES, "(^[X1 : (srt > srt)] : ((^[X1 : srt] : (X1))))" }, 
      {PRETTY,     "(λX1 : (srt → srt) : ((λX1 : srt : (X1))))" }, 
      {TPTP,       "(^[X1 : (srt > srt)] : ((^[X1 : srt] : (X1))))" } }
  );
}

TEST_FUN(hol_print_2) {
  env.setHigherOrder(true);

  auto srt = Defs::instance()->srt;
  auto fSrt = Defs::instance()->fSrt;
  auto x0 = Defs::instance()->x0;
  auto x1 = Defs::instance()->x1;
  auto f = Defs::instance()->f;

  using HOL::convert::toNameless;

  runTest(
    toNameless(LAM({x0.var(), x1.var()}, {fSrt, srt}, {x1, srt})),
    { {RAW,        "vLAM(srt > srt,srt > srt,vLAM(srt,srt,db0(srt)))" },
      {DB_INDICES, "(^db0 : srt > srt. ((^db1 : srt. (db0_0))))" },
      {PRETTY,     "(λy0 : srt → srt. (λy1 : srt. y1))" },
      {TPTP,       "(^[Y0 : srt > srt]: ((^[Y1 : srt]: (Y1))))" } }
  );

  runTest(
    toNameless(LAM({x0.var(), x1.var()}, {fSrt, srt}, {APP(fSrt, x0, x1), srt})),
    { {RAW,        "vLAM(srt > srt,srt > srt,vLAM(srt,srt,vAPP(srt,srt,db1(srt > srt),db0(srt))))" },
      {DB_INDICES, "(^db0 : srt > srt. ((^db1 : srt. (db1_1 @ db0_0))))" },
      {PRETTY,     "(λy0 : srt → srt. (λy1 : srt. (y0 y1)))" },
      {TPTP,       "(^[Y0 : srt > srt]: ((^[Y1 : srt]: (Y0 @ Y1))))" } }
  );

  runTest(
    toNameless(APP(f, x1)),
    { {RAW,        "vAPP(srt,srt,f,X1)"},
      {DB_INDICES, "(f @ X1)"},
      {PRETTY,     "(f X1)"},
      {TPTP,       "(f @ X1)"} }
  );

  runTest(
    toNameless(LAM({x1.var()}, {srt}, {APP(f, x1), srt})),
    { {RAW,        "vLAM(srt,srt,vAPP(srt,srt,f,db0(srt)))"},
      {DB_INDICES, "(^db0 : srt. (f @ db0_0))"},
      {PRETTY,     "(λy0 : srt. (f y0))"},
      {TPTP,       "(^[Y0 : srt]: (f @ Y0))"} }
  );

  runTest(
    toNameless(LAM({x1.var()}, {fSrt}, {LAM({x1.var()}, {srt}, {x1, srt}), fSrt})),
    { {RAW,        "vLAM(srt > srt,srt > srt,vLAM(srt,srt,db0(srt)))" },
      {DB_INDICES, "(^db0 : srt > srt. ((^db1 : srt. (db0_0))))" },
      {PRETTY,     "(λy0 : srt → srt. (λy1 : srt. y1))" },
      {TPTP,       "(^[Y0 : srt > srt]: ((^[Y1 : srt]: (Y1))))" }}
  );
}

#undef LAM
#undef APP