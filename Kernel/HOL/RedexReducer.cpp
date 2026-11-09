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
 * @file RedexReducer.cpp
 */

#include "Kernel/HOL/RedexReducer.hpp"
#include "Kernel/HOL/TermShifter.hpp"
#include "Kernel/HOL/HOL.hpp"

TermList RedexReducer::reduce(TermList head, TermList arg)
{
  ASS(head.isLambdaTerm());
  _replace = 0;
  _t2 = arg;
  return transform(head.lambdaBody());
}

TermList RedexReducer::transformSubterm(TermList t) {
  if (t.deBruijnIndex().isSome()) {
    unsigned index = t.deBruijnIndex().unwrap();
    if (index == _replace) {
      // any free indices in _t2 need to be lifted by the number of extra lambdas
      // that now surround them
      return _replace == 0 ? _t2 : TermShifter::shift(_t2, _replace);
    }
    if (index > _replace) {
      // free index. replace by index 1 less as now surrounded by one fewer lambdas
      TermList sort = SortHelper::getResultSort(t.term());
      return HOL::getDeBruijnIndex(index - 1, sort);
    }
  }

  return t;
}
