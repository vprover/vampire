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
 * @file SubtermReplacer.hpp
 */

#ifndef __SubtermReplacer__
#define __SubtermReplacer__

#include "Kernel/HOL/TermShifter.hpp"

using namespace Kernel;

/**
 * The class SubtermReplacer allows to replace all occurrences of one subterm by another.
 *
 * In contrast to EqHelper::replace free de Bruijn indices of the new subterm can be automatically
 * lifted in order to avoid name capture.
 *
 * See also tHOL_SubtermReplacer.cpp for accompanying unit tests of this class.
 */
class SubtermReplacer {
public:
  SubtermReplacer(TermList what, TermList by, bool liftFree)
    : _what(what), _by(by), _liftFreeIndices(liftFree)
  { ASS(what.isVar() || by.isVar() || SortHelper::getResultSort(what.term()) == SortHelper::getResultSort(by.term())); }

  inline TermList replace(TermList t) {
    return holTermTransform(t,
      [this](TermList t, unsigned lambdaLevel) {
        if (t == _what) {
          if (_liftFreeIndices && lambdaLevel != 0)
            return TermShifter::shift(_by, lambdaLevel);
          return _by;
        }

        return t;
      },
      [] (TermList orig, TermList newTerm) { return orig == newTerm; }
    );
  }

private:
  TermList _what;
  TermList _by;

  bool _liftFreeIndices; // true if need to lift free indices in _by
};

#endif // __SubtermReplacer__
