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

/**
 * The class TermShifter implements functionality to increment or decrement free de Bruijn indices
 * occurring in a given term.
 * A de Bruijn index is free, if it points "outside" the term.
 * For example, in the nameless term t = "(λ. f db_0) db_0", only the rightmost occurrence of db_0 is free.
 *
 * The shift function returns a pair consisting of the transformed term
 * as well the minimum free de Bruijn index found while traversing the term.
 *
 * Example:
 * TermTransformer::shift(t, 2) ~> { "(λ. f db_0) db_2", Option<unsigned>(0) }
 *
 * See also tTermShifter.cpp for accompanying unit tests of this class.
 */
class TermShifter : public TermTransformer
{
public:
  explicit TermShifter(int shiftBy)
    : TermTransformer(false),
      _shiftBy(shiftBy) {}

  // positive value -> shift up
  // negative -> shift down
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

private:
  unsigned _cutOff = 0; // any index higher than _cutOff is a free index
  int _shiftBy; // the amount to shift a free index by
  Option<unsigned> _minFreeIndex = Option<unsigned>();
};

#endif // __TermShifter__
