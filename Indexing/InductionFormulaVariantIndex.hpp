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
 * @file InductionFormulaVariantIndex.hpp
 * Defines class InductionFormulaVariantIndex.
 */


#ifndef __InductionFormulaVariantIndex__
#define __InductionFormulaVariantIndex__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"

#include "Shell/Options.hpp"

#include "LiteralSubstitutionTree.hpp"

namespace Inferences {
  struct InductionContext;
}

namespace Indexing {

using namespace Lib;
using namespace Kernel;

class InductionFormulaVariantIndex
{
public:
  InductionFormulaVariantIndex(bool strengthenHyp)
    : _strengthenHyp(strengthenHyp) {}

  struct Entry {
    void add(ClauseStack&& cls, Substitution&& subst) {
      for (const auto& cl : cls) {
        cl->setStore(Clause::ACTIVE);
      }
      _st.push(make_pair(cls, subst));
    }
    const Stack<pair<ClauseStack,Substitution>> get() const {
      return _st;
    }
  private:
    Stack<pair<ClauseStack,Substitution>> _st;
  };

  bool findOrInsert(const Inferences::InductionContext& context, Entry*& e);
private:
  DHMap<Stack<LiteralStack>,Entry> _groundMap;
  LiteralSubstitutionTree _nonGroundUnits;

  DHMap<TermList,TermList> _blanks;
  const bool _strengthenHyp;
};

};

#endif /* __InductionFormulaVariantIndex__ */
