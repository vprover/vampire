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

  return app(sort.domain(), sort.result(), head, arg);
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
  return TermList(shared ? Term::create(app, 4, args.begin())
                         : Term::createNonShared(app, 4, args.begin()));
}

TermList HOL::create::app(TermList sort, TermList head, TermStack& terms) {
  ASS(head.isVar() || SortHelper::getResultSort(head.term()) == sort)

  TermList res = head;
  TermList s1, s2;

  for (std::size_t i = terms.size(); i > 0; i--) {
    s1 = getNthArg(sort, 1);
    s2 = getResultAppliedToNArgs(sort, 1);
    res = app(s1, s2, res, terms[i-1]);
    sort = s2;
  }

  return res;
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

TermList HOL::create::lambda(TypedTermList var, TypedTermList body) {
  return TermList(lambda({var.var()}, {var.sort()}, body));
}

TermList HOL::create::namelessLambda(TermList varSort, TermList termSort, TermList term) {
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

TermList HOL::create::surroundWithLambdas(TermList t, TermStack& sorts, bool fromTop) {
  ASS(t.isTerm())

  TermList sort = SortHelper::getResultSort(t.term());
  return surroundWithLambdas(t, sorts, sort, fromTop);
}

TermList HOL::create::surroundWithLambdas(TermList t, TermStack& sorts, TermList sort, bool fromTop) {
  if (!fromTop) { // TODO fromTop is very hacky. See if can merge these two into one loop
    for (unsigned i = 0; i < sorts.size(); i++) {
      t = namelessLambda(sorts[i], sort, t);
      sort = AtomicSort::arrowSort(sorts[i], sort);
    }
  } else {
    for(auto i = sorts.size(); i > 0; i--) {
      t = namelessLambda(sorts[i-1], sort, t);
      sort = AtomicSort::arrowSort(sorts[i-1], sort);
    }
  }

  return t;
}