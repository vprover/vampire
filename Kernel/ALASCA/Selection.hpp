/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __ALASCA_Selection__
#define __ALASCA_Selection__


#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/LiteralSelectorOptions.hpp"

namespace Kernel {
  class AlascaSelector {

    // TODO make options
    LiteralSelectors::SelectorMode _mode;
    bool _reversePolarity;

    AlascaSelector(LiteralSelectors::SelectorMode mode, bool reversePolarity)
      : _mode(std::move(mode))
      , _reversePolarity(reversePolarity) {}

    friend struct AlascaSelectorDispatch;
  public:

    template<class LiteralSelector>
    static AlascaSelector fromType(bool reverseLcm = false)
    { return AlascaSelector(LiteralSelectors::SelectorMode(TL::Token<MaximalLiteralSelector>{}), reverseLcm); }

    static Option<AlascaSelector> fromNumber(int number) {
      return LiteralSelectors::getSelectorType(abs(number))
        .map([&](auto mode) {
            return AlascaSelector(std::move(mode), number < 0);
        });
    }
    // TODO make an array class that doesn't have any capacity slack
    Map<Clause* , Stack<SelectedAtom>> _cache;
    Stack<SelectedAtom> computeSelected(Stack<SelectedAtom> atoms, Ordering* ord) const;
  public:
    auto selected(Clause* cl, Ordering* ord)
    {
      return arrayIter(_cache.getOrInit(cl, [&]() {
            return computeSelected(SelectedAtom::iter(cl).collectStack(), ord);
      }));
    }
  };
};

#endif
