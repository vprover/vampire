/*
* This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"

#define DECL_ATOMIC_SORT(name) \
  TermList name = TermList(AtomicSort::createConstant(#name));

#define DECL_ARROW_SORT(name, from, to) \
  TermList name = TermList(AtomicSort::arrowSort(from, to));

#define DECL_VAR(name, index, sort) \
  std::pair<TermList, TermList> name = {TermList::var(index), sort};

#define DECL_CONST(name, sort) \
  unsigned name ## Index = env.signature->addFunction(#name, 0); \
  env.signature->getFunction(name ## Index)->setType(OperatorType::getFunctionType({}, sort)); \
  std::pair<TermList, TermList> name = {TermList(Term::createConstant(name ## Index)), sort};


TypedTermList AP(TypedTermList lhs, TypedTermList rhs) {
  ASS(lhs.sort().isArrowSort())

  auto [domain, result] = lhs.sort().asPair();

  if (domain != rhs.sort()) {
    std::cout << lhs << " @ " << rhs << std::endl;
  }

  ASS(domain == rhs.sort());

  // TODO MH
  return {HOL::app(lhs.sort(), lhs, rhs), result};
}

std::pair<TermList, TermList> LAM(std::pair<TermList, TermList> typedVar, std::pair<TermList, TermList> typedTerm) {

  auto [var, varSort] = typedVar;
  auto [term, termSort] = typedTerm;

  auto* boundVar = new VList(var.var());
  auto* boundVarSort = new SList(varSort);
  Term* lambdaTerm = Term::createLambda(term, boundVar, boundVarSort, termSort);

  return {TermList(lambdaTerm), TermList(AtomicSort::arrowSort(varSort, termSort))};
}

TEST_FUN(hol_print_1) {
  env.setHigherOrder(true);

  DECL_ATOMIC_SORT(srt)
  DECL_ARROW_SORT(fSrt, srt, srt)
  DECL_VAR(x0, 0, srt)
  DECL_VAR(x1, 1, srt)
  DECL_CONST(f, fSrt)

  auto term = LAM(x1, AP(f, x1));

  std::cout << "hallo\n";
}