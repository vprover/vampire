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
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/RobSubstitution.hpp"

namespace Inferences {
  struct InductionContext;
}

namespace Indexing {

using namespace Lib;
using namespace Kernel;
using Key = std::pair<Stack<LiteralStack>,std::pair<Literal*,Literal*>>;

struct InductionInstance {
  ClauseStack cls;
  RobSubstitution subst;
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
    void add(ClauseStack&& cls, RobSubstitution&& subst) {
      if (cls.isEmpty()) {
        return;
      }
      // Increase refcount of each clause so that no deallocation
      // occurs due to all children being redundant.
      for (const auto& cl : cls) {
        cl->incRefCnt();
      }
      _indInstances.push({ std::move(cls), std::move(subst) });
    }
    const Stack<InductionInstance>& getInductionInstances() const
    { return _indInstances; }

  private:
    Stack<InductionInstance> _indInstances;
  };

  static Key represent(const Inferences::InductionContext& context);

  bool findOrInsert(const Inferences::InductionContext& context, Entry*& e, Literal* bound1 = nullptr, Literal* bound2 = nullptr);
private:
  DHMap<Key,Entry> _map;
};

}

#endif /* __InductionFormulaIndex__ */
