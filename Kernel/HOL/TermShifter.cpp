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
  return TermShifter(shiftBy).transform(term);
}

TermList TermShifter::transformSubterm(TermList t) {
  auto dbi = t.deBruijnIndex();
  if (dbi.isSome()) {
    unsigned index = dbi.unwrap();
    // free index. lift
    if (index >= _cutOff && _shiftBy != 0) {
      TermList sort = SortHelper::getResultSort(t.term());
      ASS(_shiftBy >= 0 || index >= std::abs(_shiftBy));
      return HOL::getDeBruijnIndex(static_cast<int>(index) + _shiftBy, sort);
    }
  }
  return t;
}

unsigned TermShifter::minFreeDBIndex(TermList t)
{
  return t.freeDBIndices() ? t.freeDBIndices()->head() : UINT_MAX;
}
