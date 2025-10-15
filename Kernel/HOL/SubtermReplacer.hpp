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

#include "Kernel/SortHelper.hpp"
#include "Kernel/TermTransformer.hpp"

using namespace Kernel;

class SubtermReplacer : public TermTransformer {
public:
  SubtermReplacer(TermList what, TermList by, bool liftFree = false)
      : TermTransformer(false),
        _what(what),
        _by(by),
        _liftFreeIndices(liftFree),
        _shiftBy(0) {
    ASS(what.isVar() || by.isVar() || SortHelper::getResultSort(what.term()) == SortHelper::getResultSort(by.term()));
    // dontTransformSorts();
  }

  TermList replace(TermList t) {
    return transform(t);
  }

  TermList transformSubterm(TermList t) override;

  void onTermEntry(Term* t) override;
  void onTermExit(Term* t) override;

private:
  TermList _what;
  TermList _by;

  bool _liftFreeIndices; // true if need to lift free indices in _what
  int _shiftBy; // the amount to shift a free index by
};

#endif // __SubtermReplacer__
