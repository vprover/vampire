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

namespace HOL {

  using Kernel::Term;
  
inline bool isTrue(TermList term) {
  return term.isTerm() && env.signature->isFoolConstantSymbol(true, term.term()->functor());
}

inline bool isFalse(TermList term) {
  return term.isTerm() && env.signature->isFoolConstantSymbol(false, term.term()->functor());
}

std::string toString(const Term &term, bool topLevel);

TermList matrix(TermList t);
void getHeadAndArgs(TermList term, TermList &head, Kernel::TermStack &args);

TermList getNthArg(TermList arrowSort, unsigned argNum);
TermList getResultAppliedToNArgs(TermList arrowSort, unsigned argNum);
unsigned getArity(TermList sort);
TermList getDeBruijnIndex(int index, TermList sort);
} // namespace HOL

namespace HOL::create {
  TermList app(TermList sort, TermList head, TermList arg);
  TermList app(TermList head, TermList arg);
  TermList app(TermList s1, TermList s2, TermList arg1, TermList arg2, bool shared = true);

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

  Term *lambda(unsigned var, TermList varSort, Kernel::TypedTermList body);

  TermList namelessLambda(TermList varSort, TermList termSort, TermList term);
  TermList namelessLambda(TermList varSort, TermList term);
} // namespace HOL::create

namespace HOL::convert {
TermList toNameless(Term* term);
TermList toNameless(TermList term);

} // namespace HOL::convert

#endif // HOL_HPP
