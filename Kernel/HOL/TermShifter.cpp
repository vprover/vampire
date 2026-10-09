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
  if (t.isVar()) {
    return UINT_MAX;
  }
  ASS(!t.term()->isSort());

  auto dbi = t.term()->deBruijnIndex();
  if (dbi.isSome()) {
    return dbi.unwrap();
  }

  unsigned cutoff = 0;
  unsigned res = UINT_MAX;
  Recycled<Stack<std::pair<const Term*, const TermList*>>> todo;
  auto pushTodo = [&cutoff,&todo](auto t) {
    if (t->isLambdaTerm()) {
      cutoff++;
    }
    todo->emplace(t, t->termArgs());
  };
  pushTodo(t.term());

  while (todo->isNonEmpty()) {
    auto [curr, args] = todo->top();

    if (args->isEmpty()) {
      todo->pop();
      if (curr->isLambdaTerm()) {
        cutoff--;
      }
      continue;
    }
    todo->setTop({ curr, args->next() });

    if (args->isVar()) {
      continue;
    }

    auto arg = args->term();
    dbi = arg->deBruijnIndex();
    if (dbi.isSome()) {
      auto index = dbi.unwrap();
      if (index >= cutoff) {
        res = std::min(res, index - cutoff);
      }
      continue;
    }
    pushTodo(arg);
  }
  return res;
}
