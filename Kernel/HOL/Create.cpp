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

TermList HOL::create::app(TermList sort, TermList head, const TermStack& terms, bool fromTop) {
  ASS(head.isVar() || SortHelper::getResultSort(head.term()) == sort)

  TermList res = head;

  if (fromTop) {
    for (const auto& arg : iterTraits(terms.iter())) {
      TermList s1 = sort.domain();
      TermList s2 = sort.result();
      res = app(s1, s2, res, arg);
      sort = s2;
    }
  } else {
    for (const auto& arg : terms) {
      TermList s1 = sort.domain();
      TermList s2 = sort.result();
      res = app(s1, s2, res, arg);
      sort = s2;
    }
  }

  return res;
}

TermList HOL::create::app(TermList head, const TermStack& terms, bool fromTop) {
  ASS(head.isTerm())

  return app(SortHelper::getResultSort(head.term()), head, terms, fromTop);
}

TermList HOL::create::top() {
  return TermList(Term::foolTrue());
}

TermList HOL::create::bottom() {
  return TermList(Term::foolFalse());
}

TermList HOL::create::conj() {
  static const auto conjProxy = env.signature->getBinaryProxy("vAND");

  return TermList(Term::createConstant(conjProxy));
}

TermList HOL::create::disj() {
  static const auto disjProxy = env.signature->getBinaryProxy("vOR");

  return TermList(Term::createConstant(disjProxy));
}

TermList HOL::create::imp() {
  static const auto impProxy = env.signature->getBinaryProxy("vIMP");

  return TermList(Term::createConstant(impProxy));
}

TermList HOL::create::equality(TermList sort) {
  static const auto eqProxy = env.signature->getEqualityProxy();

  return TermList(Term::create1(eqProxy, sort));
}

TermList HOL::create::neg() {
  static const auto term = TermList(Term::createConstant(env.signature->getNotProxy()));

  return term;
}

TermList HOL::create::pi(TermList sort) {
  static const auto piProxy = env.signature->getPiSigmaProxy("vPI");

  return TermList(Term::create1(piProxy, sort));
}

TermList HOL::create::sigma(TermList sort) {
  static const auto sigmaProxy = env.signature->getPiSigmaProxy("vSIGMA");

  return TermList(Term::create1(sigmaProxy, sort));
}

TermList HOL::create::placeholder(TermList sort) {
  static const auto placeholder = env.signature->getPlaceholder();

  return TermList(Term::create1(placeholder, sort));
}

Term* HOL::create::lambda(unsigned numArgs, const unsigned* vars, const TermList* varSorts, TypedTermList body, TermList* resultExprSort) {
  auto s = new (0, sizeof(Term::SpecialTermData)) Term;
  s->makeSymbol(Term::toNormalFunctor(SpecialFunctor::LAMBDA), 0);

  auto sp = s->getSpecialData();
  sp->setLambdaExp(body.untyped());
  sp->setLambdaExpSort(body.sort());

  VSList* vsList = VSList::empty();
  for (int i = numArgs - 1; i >= 0; i--) {
    VSList::push({vars[i], varSorts[i]}, vsList);
  }
  sp->setLambdaVars(vsList);

  auto lambdaSort = AtomicSort::arrowSort(numArgs, varSorts, body.sort());
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

TermList HOL::create::surroundWithLambdas(TermList t, const TermStack& sorts, bool fromTop)
{
  ASS(t.isTerm());
  return surroundWithLambdas(t, sorts, SortHelper::getResultSort(t.term()), fromTop);
}

TermList HOL::create::surroundWithLambdas(TermList t, const TermStack& sorts, TermList sort, bool fromTop)
{
  // TODO try to merge the two for loops
  if (fromTop) {
    for (const auto& s : iterTraits(sorts.iter())) {
      t = namelessLambda(s, sort, t);
      sort = AtomicSort::arrowSort(s, sort);
    }
    return t;
  }

  for (const auto& s : sorts) {
    t = namelessLambda(s, sort, t);
    sort = AtomicSort::arrowSort(s, sort);
  }
  return t;
}