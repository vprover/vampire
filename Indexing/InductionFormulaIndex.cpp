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

using namespace Lib;
using namespace Inferences;

Stack<LiteralStack> InductionFormulaIndex::represent(const InductionContext& context)
{
  // all literals are ground and they are unique for
  // a specific induction context, so we order them
  // and index the set of sets of literals
  // TODO: It might be good to specialize for unit literals/clauses/etc.
  Stack<LiteralStack> st;
  for (const auto& kv : context._cls) {
    LiteralStack lits = kv.second;
    sort(lits.begin(), lits.end());
    st.push(lits);
  }
  sort(st.begin(), st.end(), [](const LiteralStack& lhs, const LiteralStack& rhs) {
    if (lhs.size() != rhs.size()) {
      return lhs.size() < rhs.size();
    }
    return lexicographical_compare(lhs.begin(), lhs.end(), rhs.begin(), rhs.end());
  });
  return st;
}

/**
 * Index an induction context or give back the entry for it.
 * @param context contains the relevant parts uniquely defining an induction formula conclusion
 * @param e is assigned the entry containing all induction formulas with matching the context
 *          and can be extended with new clausified induction formulas.
 */
bool InductionFormulaIndex::findOrInsert(const InductionContext& context, Entry*& e)
{
  CALL("InductionFormulaIndex::insert");
  ASS(!context._cls.empty());
  auto r = represent(context);
  return _map.getValuePtr(std::move(r), e);
}

}
