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
      if (!t.isEtaRedex()) {
        break;
      }
      t = TermShifter::shift(t.term()->lambdaBody().term()->termArg(0), -1);
    }
    return t;
  }

  bool alreadyTransformed(Term* t) override {
    return !t->hasEtaRedex();
  }
};

#endif // __EtaNormaliser__
