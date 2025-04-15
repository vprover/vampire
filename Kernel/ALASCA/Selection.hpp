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


#include "Kernel/ALASCA/Ordering.hpp"
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
    { return AlascaSelector(LiteralSelectors::SelectorMode(TL::Token<LiteralSelector>{}), reverseLcm); }

    static Option<AlascaSelector> fromNumber(int number) {
      return LiteralSelectors::getSelectorType(abs(number))
        .map([&](auto mode) {
            return AlascaSelector(std::move(mode), number < 0);
        });
    }
    // TODO make an array class that doesn't have any capacity slack
    Map<Clause* , Stack<__SelectedLiteral>> _cache;
    // Map<Clause* , Stack<SelectedAtom>> _cache;
    // TODO remove
    // Stack<SelectedAtom> computeSelected(Stack<SelectedAtom> atoms, Ordering* ord) const;
    Stack<__SelectedLiteral> computeSelected(Clause* cl, Ordering* ord) const;
  public:
    auto selected(Clause* cl, Ordering* ord)
    {
      // return assertionViolation<DummyIter<__SelectedLiteral>>();
      return arrayIter(_cache.getOrInit(cl, [&]() {
            return computeSelected(cl, ord);
      }));
    }

    // TODO 2 deprecate
    template<class Selected, class FailLogger>
    bool postUnificationCheck(Selected const& sel, unsigned varBank, AbstractingUnifier& unif, Ordering* ord, FailLogger logger) {
      if (!AlascaOrderingUtils::atomLocalMaxAfterUnif(ord, sel, sel.atomMaximality(), unif, varBank
            , [&](auto msg) { logger(Output::cat("atom not maximal: ", msg)); })) {
        return false;
      }
      if (sel.isBGSelected()) {
        return true;
      } else {
        if (!AlascaOrderingUtils::litMaxAfterUnif(ord, sel, sel.literalMaximality(), unif, varBank
              , [&](auto msg) { logger(Output::cat("literal not maximal: ", msg)); })) {
          return false;
        }
        return true;
      }
    }

    friend std::ostream& operator<<(std::ostream& out, AlascaSelector const& self)
    { self._mode.apply([&](auto x) { out << TL::TokenType<decltype(x)>::typeName(); }); return out; }

  };
};

#endif
