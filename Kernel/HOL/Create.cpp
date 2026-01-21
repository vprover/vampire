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

  return app(SortHelper::getResultSort(head.term()), head, arg);
}

TermList HOL::create::app(TermList s1, TermList s2, TermList arg1, TermList arg2, bool shared) {
  static TermStack args;

  args.reset();
  args.push(s1);
  args.push(s2);
  args.push(arg1);
  args.push(arg2);

  unsigned app = env.signature->getApp();
  return TermList(shared ? Term::create(app, 4, args.begin())
                         : Term::createNonShared(app, 4, args.begin()));
}

TermList HOL::create::app(TermList sort, TermList head, const TermStack& terms) {
  ASS(head.isVar() || SortHelper::getResultSort(head.term()) == sort)

  TermList res = head;

  for (std::size_t i = terms.size(); i > 0; i--) {
    TermList s1 = getNthArg(sort, 1);
    TermList s2 = getResultAppliedToNArgs(sort, 1);
    res = app(s1, s2, res, terms[i-1]);
    sort = s2;
  }

  return res;
}

TermList HOL::create::app(TermList head, const TermStack& terms) {
  ASS(head.isTerm())

  return app(SortHelper::getResultSort(head.term()), head, terms);
}

Term* HOL::create::lambda(unsigned numArgs, const unsigned* vars, const TermList* varSorts, TypedTermList body, TermList* resultExprSort) {
  auto s = new (0, sizeof(Term::SpecialTermData)) Term;
  s->makeSymbol(Term::toNormalFunctor(SpecialFunctor::LAMBDA), 0);

  auto sp = s->getSpecialData();
  sp->setLambdaExp(body.untyped());
  sp->setLambdaExpSort(body.sort());

  sp->setLambdaVars(VList::fromData(vars, numArgs));

  auto lambdaSort = AtomicSort::arrowSort(numArgs, varSorts, body.sort());
  sp->setLambdaVarSorts(SList::fromData(varSorts, numArgs));
  sp->setLambdaSort(lambdaSort);
  if (resultExprSort != nullptr)
    *resultExprSort = lambdaSort;

  return s;
}


TermList HOL::create::namelessLambda(TermList varSort, TermList termSort, TermList term) {
  ASS(varSort.isVar()  || varSort.term()->isSort());
  ASS(termSort.isVar() || termSort.term()->isSort());

  static const unsigned lam = env.signature->getLam();

  static TermStack args;
  args.reset();
  args.push(varSort);
  args.push(termSort);
  args.push(term);

  return TermList(Term::create(lam, 3, args.begin()));
}

TermList HOL::create::namelessLambda(TermList varSort, TermList term) {
  ASS(term.isTerm())

  TermList termSort = SortHelper::getResultSort(term.term());
  return namelessLambda(varSort, termSort, term);
}

TermList HOL::create::surroundWithLambdas(TermList t, TermStack& sorts, bool fromTop) {
  ASS(t.isTerm())

  TermList sort = SortHelper::getResultSort(t.term());
  return surroundWithLambdas(t, sorts, sort, fromTop);
}

TermList HOL::create::surroundWithLambdas(TermList t, TermStack& sorts, TermList sort, bool fromTop) {
  // TODO fromTop is very hacky. See if can merge these two into one loop
  if (fromTop) {
    for (auto i = sorts.size(); i-- > 0; ) {
      t = namelessLambda(sorts[i], sort, t);
      sort = AtomicSort::arrowSort(sorts[i], sort);
    }
    return t;
  }

  for (unsigned i = 0; i < sorts.size(); i++) {
    t = namelessLambda(sorts[i], sort, t);
    sort = AtomicSort::arrowSort(sorts[i], sort);
  }
  return t;
}