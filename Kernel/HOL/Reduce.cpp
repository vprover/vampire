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

TermList HOL::reduce::betaNF(TermList t, unsigned *reductions) {
  BetaNormaliser bn;
  const auto term = bn.normalise(t);
#if VDEBUG
  if (reductions != nullptr) {
    *reductions = bn.reductions;
  }
#endif

  return term;
}

TermList HOL::reduce::etaNF(TermList t) {
  return EtaNormaliser2().normalise(t);
}

TermList HOL::reduce::betaEtaNF(TermList t) {
  return etaNF(betaNF(t));
}
