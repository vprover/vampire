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

#define DECL_ATOMIC_SORT(name) \
  TermList name = TermList(AtomicSort::createConstant(#name));

#define DECL_ARROW_SORT(name, from, to) \
  TermList name = TermList(AtomicSort::arrowSort(from, to));

#define DECL_VAR(name, index) \
  TermList name = TermList::var(index);

#define DECL_CONST(name, sort) \
  unsigned name ## Index = env.signature->addFunction(#name, 0); \
  env.signature->getFunction(name ## Index)->setType(OperatorType::getFunctionType({}, sort)); \
  TermList name = TermList(Term::createConstant(name ## Index));

TEST_FUN(hol_print_1) {
  env.setHigherOrder(true);

  DECL_ATOMIC_SORT(srt)
  DECL_ARROW_SORT(fSrt, srt, srt)
  DECL_VAR(x0, 0)
  DECL_VAR(x1, 1)
  DECL_CONST(f, fSrt)

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