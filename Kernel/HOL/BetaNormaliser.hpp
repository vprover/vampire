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
 * @file BetaNormaliser.hpp
 */

#ifndef __BetaNormaliser__
#define __BetaNormaliser__

#include "Kernel/TermTransformer.hpp"
#include "Kernel/HOL/RedexReducer.hpp"

using namespace Kernel;

// reduce a term to normal form
// uses a applicative order reduction strategy
// Currently use a leftmost outermost strategy
// An innermost strategy is theoretically more efficient
// but is difficult to write iteratively TODO
struct BetaNormaliser : public BottomUpTermTransformer {
#if VDEBUG
  unsigned reductions = 0;
#endif

  BetaNormaliser() : BottomUpTermTransformer(/*transformSorts=*/false) {}

  TermList normalise(TermList t) { return transform(t); }

  TermList transformSubterm(TermList t) override {
    if (!t.isRedex()) {
      return t;
    }
    DEBUG_CODE(++reductions;)
    // a substitution can create new redexes, call transform again
    return transform(RedexReducer().reduce(t.lhs(), t.rhs()));
  }

  bool alreadyTransformed(Term* t) override {
    return !t->hasRedex();
  }
};

#endif // __BetaNormaliser__
