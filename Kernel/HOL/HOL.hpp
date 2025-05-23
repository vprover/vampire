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

namespace HOL {

  inline bool isTrue(TermList term) {
    return term.isTerm() && env.signature->isFoolConstantSymbol(true, term.term()->functor());
  }

  inline bool isFalse(TermList term) {
    return term.isTerm() && env.signature->isFoolConstantSymbol(false, term.term()->functor());
  }

  std::string toString(const Kernel::Term& term, bool topLevel);

  TermList matrix(TermList t);
  void getHeadAndArgs(TermList term, TermList& head, Kernel::TermStack & args);

} // namespace HOL

#endif //HOL_HPP
