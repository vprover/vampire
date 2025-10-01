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
 * @file TermShifter.cpp
 */

#include "Kernel/HOL/TermShifter.hpp"
#include "Kernel/HOL/HOL.hpp"

TermList TermShifter::shift(TermList term, int shiftBy) {
  _cutOff = 0;
  _shiftBy = shiftBy;

  TermList transformed = transformSubterm(term);
  return (transformed != term) ? transformed
                               : transform(term);
}

TermList TermShifter::transformSubterm(TermList t) {
  if (t.deBruijnIndex().isSome()) {
    unsigned index = t.deBruijnIndex().unwrap();
    if (index >= _cutOff) {
      // free index. lift
      if (_shiftBy != 0) {
        TermList sort = SortHelper::getResultSort(t.term());
        ASS(_shiftBy >= 0 || index >= std::abs(_shiftBy));
        return HOL::getDeBruijnIndex(static_cast<int>(index) + _shiftBy, sort);
      }
      auto j = index - _cutOff;
      if (j < _minFreeIndex || _minFreeIndex == -1)
        _minFreeIndex = static_cast<int>(j);
    }
  }
  return t;
}
