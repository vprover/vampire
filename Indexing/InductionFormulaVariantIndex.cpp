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
 * @file InductionFormulaVariantIndex.cpp
 * Implements class InductionFormulaVariantIndex.
 */

#include "InductionFormulaVariantIndex.hpp"

#include "Inferences/Induction.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Inferences;

Stack<LiteralStack> getSortedLiterals(const InductionContext& context)
{
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

// returns true iff the induction formula is not done yet
bool InductionFormulaVariantIndex::findOrInsert(const InductionContext& context, Entry*& e)
{
  CALL("InductionFormulaVariantIndex::insert");
  ASS(!context._cls.empty());

  if (context.isSingleLiteral() && _strengthenHyp) {
    // unsigned var = 0;
    // auto lit = *context._cls.begin()->second.begin();
    // SkolemSquashingTermReplacement tr(context._indTerm,_blanks.get(srt),var);
    // Literal* rep = tr.transform(lit);
    // // If we strengthen the literal there might be an arbitrary number of
    // // induction terms apart from the main one, so it is easier to replace
    // // the rest with variables and check for variants in an index.
    // // Otherwise there is only one term to replace and it gives a unique
    // // literal, so a pointer check is sufficient.
    // if (_nonGroundUnits.getVariants(rep, false, false).hasNext()) {
    //   return false;
    // }
    // _nonGroundUnits.insert(rep, nullptr);
    // return true;
  }
  if (context._cls.size() == 1) {
    // do simple clause indexing with hypothesis strengthening
  }

  auto st = getSortedLiterals(context);
  return _groundMap.getValuePtr(st, e);
}

}
