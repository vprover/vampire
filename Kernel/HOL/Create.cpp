/*
* This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Create.cpp
 */

#include "Kernel/HOL/HOL.hpp"

using Kernel::Term;

TermList HOL::create::app(TermList sort, TermList head, TermList arg) {
  ASS(sort.isArrowSort())

  auto s1 = getNthArg(sort, 1);
  auto s2 = getResultAppliedToNArgs(sort, 1);

  // auto s1 = sort.domain();
  // auto s2 = sort.result();

  return app(s1, s2, head, arg);
}

TermList HOL::create::app(TermList head, TermList arg) {
  ASS(head.isTerm())

  return app(Kernel::SortHelper::getResultSort(head.term()), head, arg);
}

TermList HOL::create::app(TermList s1, TermList s2, TermList arg1, TermList arg2, bool shared) {
  static Kernel::TermStack args;

  args.reset();
  args.push(s1);
  args.push(s2);
  args.push(arg1);
  args.push(arg2);

  unsigned app = env.signature->getApp();
  if (shared) {
    return TermList(Term::create(app, 4, args.begin()));
  }
  return TermList(Term::createNonShared(app, 4, args.begin()));
}

Term* HOL::create::lambda(std::initializer_list<unsigned> vars, std::initializer_list<TermList> varSorts, Kernel::TypedTermList body) {

  ASS_EQ(vars.size(), varSorts.size())

  auto s = new (0, sizeof(Term::SpecialTermData)) Term;
  s->makeSymbol(Term::toNormalFunctor(Kernel::SpecialFunctor::LAMBDA), 0);
  //should store body of lambda in args
  auto sp = s->getSpecialData();
  sp->setLambdaExp(body.untyped());
  sp->setLambdaExpSort(body.sort());

  auto varList = Kernel::VList::empty();
  for (auto it = std::rbegin(vars); it != std::rend(vars); ++it)
    varList = Kernel::VList::cons(*it, varList);
  sp->setLambdaVars(varList);

  auto sortList = Kernel::SList::empty();
  auto lambdaSort = body.sort();
  for (auto it = std::rbegin(varSorts); it != std::rend(varSorts); ++it) {
    sortList = Kernel::SList::cons(*it, sortList);
    lambdaSort = Kernel::AtomicSort::arrowSort(*it, lambdaSort);
  }
  sp->setLambdaVarSorts(sortList);
  sp->setLambdaSort(lambdaSort);

  return s;
}

TermList HOL::create::namelessLambda(TermList varSort, TermList termSort, TermList term)
{
  ASS(varSort.isVar()  || varSort.term()->isSort());
  ASS(termSort.isVar() || termSort.term()->isSort());

  static Kernel::TermStack args;
  args.reset();
  args.push(varSort);
  args.push(termSort);
  args.push(term);
  unsigned lam = env.signature->getLam();
  return TermList(Term::create(lam, 3, args.begin()));
}

TermList HOL::create::namelessLambda(TermList varSort, TermList term) {
  ASS(term.isTerm())

  TermList termSort = Kernel::SortHelper::getResultSort(term.term());
  return namelessLambda(varSort, termSort, term);
}