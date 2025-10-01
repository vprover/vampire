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
 * @file BetaNormaliser.cpp
 */

#include "Kernel/HOL/BetaNormaliser.hpp"
#include "Kernel/HOL/RedexReducer.hpp"
#include "Kernel/HOL/HOL.hpp"

TermList BetaNormaliser::normalise(TermList t) {
  // term transformer does not work at the top level...
  t = transformSubterm(t);
  return transform(t);
}

TermList BetaNormaliser::transformSubterm(TermList t) {
  if (t.isLambdaTerm())
    return t;

  TermList head;
  TermStack args;
  HOL::getHeadAndArgs(t, head, args);

  while (HOL::canHeadReduce(head, args)) {
    t = RedexReducer().reduce(head, args);
    if (t.isLambdaTerm())
      break;
    HOL::getHeadAndArgs(t, head, args);
  }

  return t;
}

bool BetaNormaliser::exploreSubterms(TermList orig, TermList newTerm) {
  return newTerm.term()->hasRedex();
}