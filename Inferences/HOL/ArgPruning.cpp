/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "ArgPruning.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/TermIterators.hpp"

namespace Inferences {

// algorithm is based on PruneArg in https://matryoshka-project.github.io/pubs/bentkamp_phd_thesis.pdf
Clause* ArgPruning::simplify(Clause* c)
{
  DHMap<unsigned, TermStack, FnvHash, IdentityHash> varOccurrences;

  for (const auto& l : *c) {
    SubtermIterator sti(l);
    while (sti.hasNext()) {
      auto st = sti.next();
      if (st.isTerm() && !st.isApplication()) {
        continue;
      }
      auto head = st.head();
      if (head.isTerm()) {
        continue;
      }

      TermStack* ptr;
      varOccurrences.getValuePtr(head.var(), ptr);
      ptr->push(st);
      sti.right();
    }
  }

  bool modified = false;
  auto resLits = LiteralStack::fromIterator(c->iterLits());

  decltype(varOccurrences)::Iterator it(varOccurrences);
  while (it.hasNext()) {
    unsigned v;
    const auto& ts = it.nextRef(v);
    ASS(ts.isNonEmpty());

    if (ts.size()==1 && ts[0].isTerm()) {
      for (auto& l : resLits) {
        l = EqHelper::replace(l, ts[0], TermList::var(v));
      }
      modified = true;
    }
  }

  if (modified) {
    return Clause::fromStack(resLits, SimplifyingInference1(InferenceRule::ARG_PRUNING, c));
  }

  return c;
}

}
