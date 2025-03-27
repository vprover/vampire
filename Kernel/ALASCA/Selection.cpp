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
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/MaximalLiteralSelector.hpp"
#include "Kernel/OrderingUtils.hpp"

namespace Kernel {

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

struct AlascaSelectorDispatch {
  AlascaSelector const& self;

  template<class T>
  Stack<NewSelectedAtom> computeSelected(TL::Token<T>, Stack<NewSelectedAtom> atoms, Ordering* ord) {
    ASSERTION_VIOLATION_REP("TODO")
  }

  auto iterUnproductive(Stack<NewSelectedAtom> const& atoms) const
  { return arrayIter(atoms)
       .filter([](auto x) { return !x.productive(); }); }

  auto iterMax(Ordering* ord, Stack<NewSelectedAtom> const& atoms) const {
     return OrderingUtils::maxElems(atoms.size(),
                    [=](unsigned l, unsigned r)
                    { return AlascaOrderingUtils::compareAtom(ord, atoms[l], atoms[r]); },
                    [&](unsigned i)
                    { return atoms[i]; },
                    SelectionCriterion::NOT_LESS)
            .map([&](auto i) -> decltype(auto) { return atoms[i]; })
            .filter([](auto& a) { return a.match(
                  [](auto a) { return !a.isNumSort() || !a.selectedAtomicTerm().isVar(); },
                  [](auto t) { return true; }); });
  }

  Stack<NewSelectedAtom> computeSelected(TL::Token<TotalLiteralSelector>, Stack<NewSelectedAtom> atoms, Ordering* ord)
  { return atoms; }

  Stack<NewSelectedAtom> computeSelected(TL::Token<MaximalLiteralSelector>, Stack<NewSelectedAtom> atoms, Ordering* ord)
  { return iterMax(ord, atoms).cloned().collectStack(); }


  template<bool complete>
  Stack<NewSelectedAtom> computeSelected(TL::Token<GenericRndLiteralSelector<complete>>, Stack<NewSelectedAtom> atoms, Ordering* ord) {
    if (complete) {
      RStack<NewSelectedAtom> negative;
      negative->loadFromIterator(iterUnproductive(atoms));
      if (negative.size() != 0
          // && Random::getBit() // <- sometimes select all maximals even if there is negatives TODO do we want this really?
          ) {
        return { Random::getElem(*negative) };
      } else {
        return iterMax(ord, atoms).cloned().collectStack();
      }
    } else {
      return { Random::getElem(atoms) };
    }
  }

};


Stack<NewSelectedAtom> AlascaSelector::computeSelected(Stack<NewSelectedAtom> atoms, Ordering* ord) const
{
  DEBUG(0, "     all atoms: ", atoms)
  auto out = _mode.apply([&](auto token) { return AlascaSelectorDispatch{*this}.computeSelected(token, std::move(atoms), ord); });
  DEBUG(0, "selected atoms: ", out)
  return out;
}

} // namespace Kernel
