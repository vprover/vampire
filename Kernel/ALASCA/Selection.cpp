/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Selection.hpp"
#include "Kernel/ALASCA/Ordering.hpp"
#include "Kernel/OrderingUtils.hpp"

namespace Kernel {

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

Stack<NewSelectedAtom> AlascaSelector::computeSelected(Stack<NewSelectedAtom> atoms, Ordering* ord) {
  // TODO
  // auto out =  arrayIter(std::move(atoms))
  //   .filter([](auto a) { return a.match(
  //         [](auto a) { return !a.selectedAtomicTerm().isVar(); },
  //         [](auto t) { return true; }); })
  //   .template collect<Stack>()
  // ;
  DEBUG(0, "     all atoms: ", atoms)

  auto out = OrderingUtils::maxElems(atoms.size(), 
                  [=](unsigned l, unsigned r) 
                  { return AlascaOrderingUtils::compareAtom(ord, atoms[l], atoms[r]); },
                  [&](unsigned i)
                  { return atoms[i]; },
                  SelectionCriterion::NOT_LESS)
          .map([&](auto i) { return atoms[i]; })
          .filter([](auto a) { return a.match(
                [](auto a) { return !a.isNumSort() || !a.selectedAtomicTerm().isVar(); },
                [](auto t) { return true; }); })
          .collectStack();
  // if (auto i = arrayIter(out).findPosition([](auto x) { return !x.productive(); })) {
  //     out = {out[*i]};
  // }
  DEBUG(0, "selected atoms: ", out)
  return out;
}

} // namespace Kernel
