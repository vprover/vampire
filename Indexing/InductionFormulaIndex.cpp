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
 * @file InductionFormulaIndex.cpp
 * Implements class InductionFormulaIndex.
 */

#include "InductionFormulaIndex.hpp"

#include "Inferences/Induction.hpp"

namespace Indexing
{

using namespace std;
using namespace Lib;
using namespace Inferences;

Key InductionFormulaIndex::represent(const InductionContext& context)
{
  // check that the elements in the literal stacks are sorted, for sharing
  ASS(iterTraits(context._cls.iter()).all([](const auto& e) { return is_sorted(e.second.begin(), e.second.end()); }));
  ASS(is_sorted(context._cls.begin(), context._cls.end(), [](const auto& e1, const auto& e2) { return e1.second < e2.second; }));
  // all literals are ground and they are unique for
  // a specific induction context, so we order them
  // and index the set of sets of literals
  // TODO: It might be good to specialize for unit literals/clauses/etc.
  Key k;
  for (const auto& kv : context._cls) {
    k.first.push(kv.second);
  }
  return k;
}

/**
 * Index an induction context or give back the entry for it.
 * @param context contains the relevant parts uniquely defining an induction formula conclusion
 * @param e is assigned the entry containing all induction formulas with matching the context
 *          and can be extended with new clausified induction formulas.
 * @param bound1 only used with integer induction to distinguish bounds from other literals
 * @param bound2 only used with integer induction to distinguish bounds from other literals
 */
bool InductionFormulaIndex::findOrInsert(const InductionContext& context, Entry*& e, Literal* bound1, Literal* bound2)
{
  ASS(context._cls.isNonEmpty());
  auto k = represent(context);
  k.second.first = bound1;
  k.second.second = bound2;
  return _map.getValuePtr(std::move(k), e);
}

}
