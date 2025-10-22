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

TermList RedexReducer::reduce(TermList head, TermStack& args) {
  ASS(HOL::canHeadReduce(head, args))

  _replace = 0;
  TermList t1 = head.lambdaBody();
  TermList t1Sort = *head.term()->nthArgument(1);
  _t2 = args.pop();

  return HOL::create::app(t1Sort, transform(t1), args);
}

TermList RedexReducer::transformSubterm(TermList t) {
  if (t.deBruijnIndex().isSome()) {
    unsigned index = t.deBruijnIndex().unwrap();
    if (index == _replace) {
      // any free indices in _t2 need to be lifted by the number of extra lambdas
      // that now surround them
      return _replace == 0 ? _t2 : TermShifter::shift(_t2, _replace).first;
    }
    if (index > _replace) {
      // free index. replace by index 1 less as now surrounded by one fewer lambdas
      TermList sort = SortHelper::getResultSort(t.term());
      return HOL::getDeBruijnIndex(index - 1, sort);
    }
  }

  return t;
}
