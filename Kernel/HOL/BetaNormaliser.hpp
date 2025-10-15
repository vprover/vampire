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

using namespace Kernel;

// reduce a term to normal form
// uses a applicative order reduction strategy
// Currently use a leftmost outermost strategy
// An innermost strategy is theoretically more efficient
// but is difficult to write iteratively TODO
class BetaNormaliser : public TermTransformer {
  unsigned reductions = 0;
public:
  BetaNormaliser() : TermTransformer(false) {}

  unsigned getReductions() const {
    return reductions;
  }

  TermList normalise(TermList t);

  TermList transformSubterm(TermList t) override;

  bool exploreSubterms(TermList orig, TermList newTerm) override;
};

#endif // __BetaNormaliser__
