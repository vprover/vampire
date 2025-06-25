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


#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/Ordering.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/LiteralSelectorOptions.hpp"

namespace Kernel {
  class AlascaSelector {
    // TODO make options
    LiteralSelectors::SelectorMode _mode;
    bool _reversePolarity;
    Inferences::SimplifyingGeneratingInference* _inf = nullptr;
    Ordering* ord;

    friend struct AlascaSelectorDispatch;
  public:
    AlascaSelector(AlascaSelector &&) = default;

    AlascaSelector(Ordering* ord, LiteralSelectors::SelectorMode mode, bool reversePolarity)
      : _mode(std::move(mode))
      , _reversePolarity(reversePolarity) 
      , ord(ord) 
      {}

#if VDEBUG
    void setOrdering(Ordering* ord) { this->ord = ord; }
#endif

    void setLookaheadInferenceEngine(Inferences::SimplifyingGeneratingInference* inf) { _inf = inf; }

    // template<class LiteralSelector>
    // static AlascaSelector fromType(Ordering* ord, bool reverseLcm = false)
    // { return AlascaSelector(ord, LiteralSelectors::SelectorMode(TL::Token<LiteralSelector>{}), reverseLcm); }

    static Option<AlascaSelector> fromNumber(Ordering* ord, int number) {
      return LiteralSelectors::getSelectorType(abs(number))
        .map([&](auto mode) {
            return AlascaSelector(ord, std::move(mode), number < 0);
        });
    }

    // TODO make an array class that doesn't have any capacity slack
    /* we store a boolean for every clause, marking whether the given clauses's literals have been BachmairGanzinger-selected, or whether the selected literals are just maximal. true means BG selected, false means maximal, no entry means selection hasn't taken place yet. */
    Map<unsigned , bool> _isBgSelected;
    mutable Map<TypedTermList, Stack<unsigned>> _maxAtoms;
    bool computeSelected(Clause* cl) const;
  public:

    template<class NumTraits>
    Stack<unsigned> const& maxAtomsNotLessStack(AlascaTermItp<NumTraits> const& t) const {
      auto key = t.toTerm();
      if (auto val = _maxAtoms.tryGet(key)) {
        return *val;
      } else {
       auto stack = OrderingUtils::maxElems(t.nSummands(),
                      [=](unsigned l, unsigned r)
                      { return ord->compare(t.summandAt(l).atom(), t.summandAt(r).atom()); },
                      [&](unsigned i)
                      { return t.summandAt(i).atom(); },
                      SelectionCriterion::NOT_LESS)
              .collectStack();

        auto& out = _maxAtoms.insert(key, std::move(stack));
        return out;
      }
    }


    template<class NumTraits>
    auto maxAtomsNotLess(AlascaTermItp<NumTraits> const& t) const 
    { return arrayIter(maxAtomsNotLessStack(t))
        .map([=](auto i) { return t.summandAt(i); }); }


    bool getSelection(Clause* cl);
    auto selected(Clause* cl)
    { 
      auto bgSelected = getSelection(cl);
      return range(0, cl->numSelected())
        .map([cl, bgSelected](auto i) {
            return __SelectedLiteral(cl, i, bgSelected);
        });
    }

    // TODO 2 deprecate
    template<class Selected, class FailLogger>
    bool postUnificationCheck(Selected const& sel, unsigned varBank, AbstractingUnifier& unif, FailLogger logger) {
      if (!AlascaOrderingUtils::atomLocalMaxAfterUnif(ord, sel, sel.localAtomicTermMaximality(), unif, varBank
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
