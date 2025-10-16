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
 * @file ToPlaceholders.cpp
 */

#include "Kernel/HOL/ToPlaceholders.hpp"
#include "Kernel/HOL/HOL.hpp"

ToPlaceholders::ToPlaceholders(std::optional<Options::FunctionExtensionality> funcExtMode)
      : TermTransformer(false),
        _nextIsPrefix(false),
        _topLevel(true),
        _mode(funcExtMode.value_or(env.options->functionExtensionality())) {}

TermList ToPlaceholders::replace(TermList term) {
  TermList transformed = transformSubterm(term);

  if (transformed != term)
    return transformed;

  _topLevel = false;
  return transform(term);
}

TermList ToPlaceholders::transformSubterm(TermList t) {
  if (_nextIsPrefix || t.isVar())
    return t;

  // Not expecting any unreduced redexes here
  ASS(!t.head().isLambdaTerm())

  auto sort = SortHelper::getResultSort(t.term());
  if (t.isLambdaTerm() || t.head().isVar())
    return HOL::create::placeholder(sort);

  if (_mode == Options::FunctionExtensionality::ABSTRACTION) {
    if (sort.isArrowSort() || sort.isVar() || (sort.isBoolSort() && !_topLevel)) {
      return HOL::create::placeholder(sort);
    }
  }
  return t;
}
