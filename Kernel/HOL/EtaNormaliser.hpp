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
struct EtaNormaliser : public BottomUpTermTransformer
{
  EtaNormaliser() : BottomUpTermTransformer(/*transformSorts=*/false) {}
  TermList normalise(TermList t) { return transform(t); }

private:
  TermList transformSubterm(TermList t) override {
    while (t.isEtaRedex()) {
      t = TermShifter::shift(t.term()->lambdaBody().term()->termArg(0), -1);
    }
    return t;
  }

  bool alreadyTransformed(Term* t) override {
    return !t->hasEtaRedex();
  }
};

#endif // __EtaNormaliser__
