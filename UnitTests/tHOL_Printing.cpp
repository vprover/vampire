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

#include <map>

TermList mkAtomicSort(const std::string& name) {
  return TermList(AtomicSort::createConstant(name));
}

TermList mkConst(const std::string& name, TermList sort) {
  unsigned nameIndex = env.signature->addFunction(name, 0);
  env.signature->getFunction(nameIndex)->setType(OperatorType::getFunctionType({}, sort));
  return TermList(Term::createConstant(nameIndex));
}

TermList LAM(std::initializer_list<unsigned> vars, std::initializer_list<TermList> varSorts, Kernel::TypedTermList body) {
  return TermList(HOL::create::lambda(vars, varSorts, body));
}

constexpr Options::HPrinting RAW = Options::HPrinting::RAW;
constexpr Options::HPrinting PRETTY = Options::HPrinting::PRETTY;
constexpr Options::HPrinting DB_INDICES = Options::HPrinting::DB_INDICES;
constexpr Options::HPrinting TPTP = Options::HPrinting::TPTP;

TEST_FUN(hol_print_1) {
  env.setHigherOrder(true);


  auto srt = mkAtomicSort("srt");
  auto fSrt = TermList(AtomicSort::arrowSort(srt, srt));
  auto x0 = TermList::var(0);
  auto x1 = TermList::var(1);
  auto f = mkConst("f", fSrt);

  const std::initializer_list<std::pair<TermList, std::map<Options::HPrinting, std::string>>> tests {
    // {LAM({x0.var(), x1.var()}, {fSrt, srt}, {x1, srt}), {
    //   {RAW,        "(^[X0 : (srt > srt), X1 : srt] : (X1))"},
    //   {PRETTY,     "(λX0 : (srt → srt), X1 : srt : (X1))"},
    //   {DB_INDICES, "(^[X0 : (srt > srt), X1 : srt] : (X1))"},
    //   {TPTP,       "(^[X0 : (srt > srt), X1 : srt] : (X1))"}
    // }},

    {LAM({x0.var(), x1.var()}, {fSrt, srt}, {HOL::create::app(fSrt, x0, x1), srt}), {
      {RAW, "(^[X0 : (srt > srt), X1 : srt] : (vAPP(srt,srt,X0,X1)))"},
      {PRETTY, "(λX0 : (srt → srt), X1 : srt : ((X0 X1)))"},
      {DB_INDICES, "(^[X0 : (srt > srt), X1 : srt] : ((X0 @ X1)))"},
      {TPTP, "(^[X0 : (srt > srt), X1 : srt] : ((X0 @ X1)))"}
    }}
  };

  for (const auto& [term, opts] : tests) {
    for (const auto& [printOpt, expected] : opts) {
      env.options->setHolPrinting(printOpt);
      std::cout << term.toString() << std::endl;
      // ASS_EQ(term.toString(), expected)
    }
  }

  // auto zero = LAM({x0.var(), x1.var()}, {fSrt, srt}, {x1, srt});
  // ASS_EQ(zero.toString(true), "(^[X0 : (srt > srt), X1 : srt] : (X1))")
  // ASS_EQ(HOL::convert::toNameless(zero).toString(true), "(^[Y0 : srt > srt]: ((^[Y1 : srt]: (Y1))))")
  //
  // auto one = LAM({x0.var(), x1.var()}, {fSrt, srt}, {HOL::create::app(fSrt, x0, x1), srt});
  // ASS_EQ(one.toString(true), "(^[X0 : (srt > srt), X1 : srt] : ((X0 @ X1)))")
  // ASS_EQ(HOL::convert::toNameless(one).toString(true), "(^[Y0 : srt > srt]: ((^[Y1 : srt]: (Y0 @ Y1))))")
  //
  // auto t1 = HOL::create::app(f, x1);
  // ASS_EQ(t1.toString(true), "f @ X1")
  // ASS_EQ(HOL::convert::toNameless(t1).toString(true), "f @ X1")
  //
  // auto t2 = LAM({x1.var()}, {srt}, {t1, srt});
  // ASS_EQ(t2.toString(true), "(^[X1 : srt] : ((f @ X1)))")
  // ASS_EQ(HOL::convert::toNameless(t2).toString(true), "(^[Y0 : srt]: (f @ Y0))")
  //
  // auto t3 = LAM({x1.var()}, {fSrt}, {LAM({x1.var()}, {srt}, {x1, srt}), fSrt});
  // std::cout << t3.toString() << std::endl;
  // // std::cout << SortHelper::getResultSort(t3.term()).toString() << std::endl;
  // std::cout << HOL::convert::toNameless(t3).toString() << std::endl; // TODO
  // // ASS_EQ(t3.toString(true), "(^[X1 : srt] : ((f @ X1)))")
}