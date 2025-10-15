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
 * @file RedexReducer.hpp
 */

#ifndef __RedexReducer__
#define __RedexReducer__

#include "Kernel/TermTransformer.hpp"

using namespace Kernel;

class RedexReducer : public TermTransformer {
public:
  RedexReducer() : TermTransformer(false) {}

  TermList reduce(TermList head, TermStack& args);
  TermList transformSubterm(TermList t) override;

  void onTermEntry(Term* t) override {
    if (t->isLambdaTerm())
      _replace++;
  }

  void onTermExit(Term* t) override {
    if (t->isLambdaTerm())
      _replace--;
  }

  bool exploreSubterms(TermList orig, TermList newTerm) override {
    return orig == newTerm && newTerm.term()->hasDeBruijnIndex();
  }

private:
  TermList _t2; // term to replace index with (^x.t1) t2
  unsigned _replace; // index to replace
};

#endif // __RedexReducer__
