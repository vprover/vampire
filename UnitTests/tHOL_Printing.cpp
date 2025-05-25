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
  env.options->setHolPrinting(Options::HPrinting::RAW);

  DECL_ATOMIC_SORT(srt)
  DECL_ARROW_SORT(fSrt, srt, srt)
  DECL_VAR(x0, 0)
  DECL_VAR(x1, 1)
  DECL_CONST(f, fSrt)

  auto t1 = HOL::create::app(f, x1);
  auto t2 = TermList(HOL::create::lambda(x1.var(), srt, {t1, srt}));

  std::cout << t1 << std::endl;
  std::cout << t2 << std::endl;

  std::cout << HOL::convert::toNameless(t1) << std::endl;
  std::cout << HOL::convert::toNameless(t2) << std::endl;
}