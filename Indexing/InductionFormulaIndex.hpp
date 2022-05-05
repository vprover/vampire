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
 * @file InductionFormulaIndex.hpp
 * Defines class InductionFormulaIndex.
 */


#ifndef __InductionFormulaIndex__
#define __InductionFormulaIndex__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Hash.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Substitution.hpp"

#include "Shell/Options.hpp"

namespace Inferences {
  struct InductionContext;
}

namespace Indexing {

using namespace Lib;
using namespace Kernel;

struct SecondaryStackHash {
  static unsigned hash(const Stack<LiteralStack>& s) {
    unsigned res = FNV32_OFFSET_BASIS;
    typename Stack<LiteralStack>::ConstIterator it(s);
    while (it.hasNext()) {
      res += it.next().length();
    }
    return res;
  }
};

class InductionFormulaIndex
{
public:
  /** Stores clausified induction formulas,
   * each associated with a substitution that
   * needs to be applied on conclusion literals
   * to get the complementary literals stored
   * in a matching InductionContext.
   */
  struct Entry {
    void add(ClauseStack&& cls, Substitution&& subst) {
      if (cls.isEmpty()) {
        return;
      }
      // Each clause is used immediately upon creation but
      // their memory will be reused by Vampire if their
      // store is NONE and all their descendants are deleted
      // due to simplifications, so we change them to active.
      for (const auto& cl : cls) {
        if (!env.options->splitInductionClauses()) {
          cl->setStore(Clause::ACTIVE);
        }
      }
      _st.push(make_pair(cls, subst));
    }
    const Stack<pair<ClauseStack,Substitution>>& get() const {
      return _st;
    }
  private:
    Stack<pair<ClauseStack,Substitution>> _st;
  };

  static Stack<LiteralStack> represent(const Inferences::InductionContext& context);

  bool findOrInsert(const Inferences::InductionContext& context, Entry*& e);
private:
  DHMap<Stack<LiteralStack>,Entry,Lib::StackHash<Lib::StlHash>,SecondaryStackHash> _map;
};

}

#endif /* __InductionFormulaIndex__ */
