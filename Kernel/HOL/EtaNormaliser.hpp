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
 * @file EtaNormaliser.hpp
 */

#ifndef __EtaNormaliser__
#define __EtaNormaliser__

#include "Kernel/TermTransformer.hpp"
#include "Kernel/HOL/TermShifter.hpp"

using namespace Kernel;

// reduce to eta short form
// normalises top down carrying out parallel eta reductions
// for terms such as ^^^.f 2 1 0
// WARNING Recursing lurks here (even during proof search!)
// This is BAD! However, an  (efficient) iterative implementation is tricky, so
// I am leaving for now.
namespace EtaNormaliser {
  TermList normalise(TermList t);
  TermList transformSubterm(TermList t);
}

struct EtaNormaliser2 : public BottomUpTermTransformer
{
  EtaNormaliser2() : BottomUpTermTransformer(/*transformSorts=*/false) {}

  TermList normalise(TermList t) { return transform(t); }
  TermList transformSubterm(TermList t) override {
    for (;;) {
      if (!t.isLambdaTerm()) {
        break;
      }
      auto lb = t.term()->lambdaBody();
      if (!lb.isApplication()) {
        break;
      }
      auto lhs = lb.term()->termArg(0);
      auto rhs = lb.term()->termArg(1);
      if (rhs.deBruijnIndex().unwrapOr(UINT_MAX) != 0) {
        break;
      }
      if (lhs.freeDBIndices() && lhs.freeDBIndices()->head() == 0) {
        break;
      }
      t = TermShifter::shift(lhs, -1);
    }
    return t;
  }

  bool alreadyTransformed(Term* t) override {
    return !t->hasLambda();
  }
};

#endif // __EtaNormaliser__
