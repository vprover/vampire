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
 * @file TermShifter.hpp
 */

#ifndef __TermShifter__
#define __TermShifter__

#include "Kernel/TermTransformer.hpp"
#include "Kernel/Term.hpp"

using namespace Kernel;

class TermShifter : public TermTransformer
{
public:
  explicit TermShifter(int shiftBy)
    : TermTransformer(false),
      _shiftBy(shiftBy) {}

  // positive value -> shift up
  // negative -> shift down
  // 0 record minimum free index
  static std::pair<TermList, Option<unsigned>> shift(TermList term, int shiftBy);
  TermList transformSubterm(TermList t) override;

  void onTermEntry(Term* t) override {
    if (t->isLambdaTerm())
      _cutOff++;
  }

  void onTermExit(Term* t) override {
    if (t->isLambdaTerm())
      _cutOff--;
  }

  bool exploreSubterms(TermList orig, TermList newTerm) override {
    // already shifted, so must be DB index and won't have subterms anyway
    return orig == newTerm && newTerm.term()->hasDeBruijnIndex();
  }

  Option<int> minFreeIndex() const {
    return (_minFreeIndex > -1) ? Option<int>(_minFreeIndex)
                                : Option<int>();
  }

private:
  unsigned _cutOff = 0; // any index higher than _cutOff is a free index
  int _shiftBy; // the amount to shift a free index by
  int _minFreeIndex = -1;
};

#endif // __TermShifter__
