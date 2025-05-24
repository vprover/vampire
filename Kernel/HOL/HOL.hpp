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

inline bool isTrue(TermList term) {
  return term.isTerm() && env.signature->isFoolConstantSymbol(true, term.term()->functor());
}

inline bool isFalse(TermList term) {
  return term.isTerm() && env.signature->isFoolConstantSymbol(false, term.term()->functor());
}

std::string toString(const Kernel::Term &term, bool topLevel);

TermList app(TermList sort, TermList head, TermList arg);
TermList app(TermList head, TermList arg);
TermList app(TermList s1, TermList s2, TermList arg1, TermList arg2, bool shared = true);

Kernel::Term *mkLambda(unsigned var, TermList varSort, Kernel::TypedTermList body);

TermList matrix(TermList t);
void getHeadAndArgs(TermList term, TermList &head, Kernel::TermStack &args);

TermList getNthArg(TermList arrowSort, unsigned argNum);
TermList getResultAppliedToNArgs(TermList arrowSort, unsigned argNum);
unsigned getArity(TermList sort);

} // namespace HOL

#endif // HOL_HPP
