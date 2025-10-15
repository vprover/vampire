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
 * @file Reduce.cpp
 */

#include "BetaNormaliser.hpp"
#include "EtaNormaliser.hpp"
#include "Kernel/HOL/HOL.hpp"

using Kernel::Term;


TermList HOL::reduce::betaNF(TermList t, unsigned *reductions) {
  auto bn = BetaNormaliser();
  const auto term = bn.normalise(t);
  if (reductions != nullptr)
    *reductions = bn.getReductions();

  return term;
}

TermList HOL::reduce::etaNF(TermList t) {
  return EtaNormaliser::normalise(t);
}

inline TermList HOL::reduce::betaEtaNF(TermList t) {
  return etaNF(betaNF(t));
}
