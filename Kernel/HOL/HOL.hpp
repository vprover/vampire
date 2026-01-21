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
 * @file HOL.hpp
 */

#ifndef HOL_HPP
#define HOL_HPP

#include "Kernel/Signature.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Lib/Environment.hpp"

/**
 * This namespace contains several helper functions to deal with higher-order terms.
 */
namespace HOL {

using Kernel::Term;

inline bool isTrue(TermList term) {
  return term.isTerm() && env.signature->isFoolConstantSymbol(true, term.term()->functor());
}

inline bool isFalse(TermList term) {
  return term.isTerm() && env.signature->isFoolConstantSymbol(false, term.term()->functor());
}

inline bool isBool(TermList term) {
  return isTrue(term) || isFalse(term);
}

std::string toString(const Term &term, bool topLevel);

TermList matrix(TermList t);
TermList getHeadAndArgs(TermList term, TermStack &args);
std::pair<TermList, TermStack> getHeadAndArgs(TermList term);

TermList getNthArg(TermList arrowSort, unsigned argNum);
TermList getResultAppliedToNArgs(TermList arrowSort, unsigned argNum);
unsigned getArity(TermList sort);
TermList getDeBruijnIndex(int index, TermList sort);

void getHeadSortAndArgs(TermList term, TermList& head, TermList& headSort, TermStack& args);
void getHeadArgsAndArgSorts(TermList t, TermList& head, TermStack& args, TermStack& argSorts);

TermList lhsSort(TermList t);
TermList rhsSort(TermList t);

TermList finalResult(TermList sort);

void getMatrixAndPrefSorts(TermList t, TermList& matrix, TermStack& sorts);

inline bool canHeadReduce(const TermList& head, const TermStack& args) {
  return head.isLambdaTerm() && args.isNonEmpty();
}

} // namespace HOL

namespace HOL::create {
  TermList app(TermList sort, TermList head, TermList arg);
  TermList app(TermList head, TermList arg);
  TermList app(TermList s1, TermList s2, TermList arg1, TermList arg2, bool shared = true);
  TermList app(TermList sort, TermList head, const TermStack& terms); // todo const termstack
  TermList app(TermList head, const TermStack& terms);

  inline TermList app2(TermList sort, TermList head, TermList arg1, TermList arg2) {
    return app(app(sort, head, arg1), arg2);
  }

  inline TermList app2(TermList head, TermList arg1, TermList arg2) {
    ASS(head.isTerm())

    return app2(Kernel::SortHelper::getResultSort(head.term()), head, arg1, arg2);
  }

  inline TermList equality(TermList sort) { return TermList(Term::create1(env.signature->getEqualityProxy(), sort)); }
  inline TermList neg() { return TermList(Term::createConstant(env.signature->getNotProxy())); }
  inline TermList pi(TermList sort) { return TermList(Term::create1(env.signature->getPiSigmaProxy("vPI"), sort)); }
  inline TermList sigma(TermList sort) { return TermList(Term::create1(env.signature->getPiSigmaProxy("vSIGMA"), sort)); }

  Term* lambda(unsigned numArgs, const unsigned* vars, const TermList* varSorts, TypedTermList body, TermList* resultExprSort = nullptr);

  TermList namelessLambda(TermList varSort, TermList termSort, TermList term);
  TermList namelessLambda(TermList varSort, TermList term);

  TermList surroundWithLambdas(TermList t, TermStack& sorts, bool fromTop = false);
  TermList surroundWithLambdas(TermList t, TermStack& sorts, TermList sort, bool fromTop = false);
} // namespace HOL::create

namespace HOL::convert {

TermList toNameless(TermList term);

inline TermList toNameless(Term* term) {
  return toNameless(TermList(term));
}

} // namespace HOL::convert

namespace HOL::reduce {
TermList betaNF(TermList t, unsigned* reductions = nullptr);
TermList etaNF(TermList t);
TermList betaEtaNF(TermList t);
} // namespace HOL::reduce

#endif // HOL_HPP
