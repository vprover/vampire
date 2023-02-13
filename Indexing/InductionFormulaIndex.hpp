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

namespace Inferences {
  struct InductionContext;
}

namespace Indexing {

using namespace Lib;
using namespace Kernel;
using namespace std;
using Key = pair<Stack<LiteralStack>,pair<Literal*,Literal*>>;

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
      // Increase refcount of each clause so that no deallocation
      // occurs due to all children being redundant.
      for (const auto& cl : cls) {
        cl->incRefCnt();
      }
      _st.push(make_pair(cls, subst));
    }
    const Stack<pair<ClauseStack,Substitution>>& get() const {
      return _st;
    }
  private:
    Stack<pair<ClauseStack,Substitution>> _st;
  };

  static Key represent(const Inferences::InductionContext& context);

  bool findOrInsert(const Inferences::InductionContext& context, Entry*& e, Literal* bound1 = nullptr, Literal* bound2 = nullptr);
private:
  DHMap<Key,Entry> _map;
};

}

#endif /* __InductionFormulaIndex__ */
