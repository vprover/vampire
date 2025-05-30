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
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"

TermList mkAtomicSort(const std::string& name) {
  return TermList(AtomicSort::createConstant(name));
}

TermList mkConst(const std::string& name, TermList sort) {
  unsigned nameIndex = env.signature->addFunction(name, 0);
  env.signature->getFunction(nameIndex)->setType(OperatorType::getFunctionType({}, sort));
  return TermList(Term::createConstant(nameIndex));
}

TEST_FUN(hol_print_1) {
  env.setHigherOrder(true);

  auto srt = mkAtomicSort("srt");
  auto fSrt = TermList(AtomicSort::arrowSort(srt, srt));
  auto x0 = TermList::var(0);
  auto x1 = TermList::var(1);
  auto f = mkConst("f", fSrt);

  auto zero = TermList(HOL::create::lambda({0, 1}, {fSrt, srt}, {x1, srt}));
  ASS_EQ(zero.toString(true), "(^[X0 : (srt > srt), X1 : srt] : (X1))")
  ASS_EQ(HOL::convert::toNameless(zero).toString(true), "(^[Y0 : srt > srt]: ((^[Y1 : srt]: (Y1))))")

  auto one = TermList(HOL::create::lambda({0, 1}, {fSrt, srt}, {HOL::create::app(fSrt, x0, x1), srt}));
  ASS_EQ(one.toString(true), "(^[X0 : (srt > srt), X1 : srt] : ((X0 @ X1)))")
  ASS_EQ(HOL::convert::toNameless(one).toString(true), "(^[Y0 : srt > srt]: ((^[Y1 : srt]: (Y0 @ Y1))))")

  auto t1 = HOL::create::app(f, x1);
  ASS_EQ(t1.toString(true), "f @ X1")
  ASS_EQ(HOL::convert::toNameless(t1).toString(true), "f @ X1")

  auto t2 = TermList(HOL::create::lambda({x1.var()}, {srt}, {t1, srt}));
  ASS_EQ(t2.toString(true), "(^[X1 : srt] : ((f @ X1)))")
  ASS_EQ(HOL::convert::toNameless(t2).toString(true), "(^[Y0 : srt]: (f @ Y0))")
}