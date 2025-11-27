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
 * @file SubtermReplacer.cpp
 */

#include "Kernel/SortHelper.hpp"
#include "SubtermReplacer.hpp"
#include "TermShifter.hpp"

SubtermReplacer::SubtermReplacer(TermList what, TermList by, bool liftFree)
      : TermTransformer(false),
        _what(what),
        _by(by),
        _liftFreeIndices(liftFree) {
  ASS(what.isVar() || by.isVar() || SortHelper::getResultSort(what.term()) == SortHelper::getResultSort(by.term()))
}

TermList SubtermReplacer::transformSubterm(TermList t) {
  if (t == _what) {
    if (_liftFreeIndices && _shiftBy != 0)
      return TermShifter::shift(_by, _shiftBy).first;
    return _by;
  }

  return t;
}

void SubtermReplacer::onTermEntry(Term* t) {
  if (t->isLambdaTerm())
    _shiftBy++;
}

void SubtermReplacer::onTermExit(Term* t) {
  if (t->isLambdaTerm()) {
    ASS(_shiftBy > 0)

    _shiftBy--;
  }
}