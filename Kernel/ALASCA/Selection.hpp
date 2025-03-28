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

    LiteralSelectors::SelectorMode _mode;
    bool _reversePolarity;
    // TODO make options

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


    // LiteralSelectors::AnySelector mode;

    // TODO make an array class that doesn't have any capacity slack
    Map<Clause* , Stack<SelectedAtom>> _cache;
    // template<class T>
    // Stack<SelectedAtom> computeSelected(TL::Token<T>, Stack<SelectedAtom> atoms, Ordering* ord);
    Stack<SelectedAtom> computeSelected(Stack<SelectedAtom> atoms, Ordering* ord) const;
    // auto iterAtoms(Clause* cl) {
    //    return cl->iterLits()
    //        .zipWithIndex() .flatMap([cl](auto l_i) {
    //          auto l = l_i.first;
    //          auto i = l_i.second;
    //          auto nl = InequalityNormalizer::normalize(l);
    //          return ifElseIter(
    //
    //              /* literals  t1 + t2 + ... + tn <> 0 */
    //              [&]() { return nl.asItp().isSome(); },
    //              [&]() {
    //                return coproductIter(nl.asItp()->applyCo([cl,i](auto itp) {
    //                    return itp.term().iterSummands()
    //                       .zipWithIndex()
    //                       .map([cl,i](auto s_i) -> SelectedAtom {
    //                           return  SelectedAtom(SelectedAtomicTerm(SelectedAtomicTermItp<decltype(itp.numTraits())>(
    //                                   cl, i, s_i.second
    //                                   )));
    //                       });
    //                }));
    //              },
    //
    //              /* literals  (~)t1 = t2  */
    //              [&]() { return nl.toLiteral()->isEquality(); },
    //              [&]() {
    //                return iterItems(0, 1)
    //                   .map([cl,i](auto j) { return SelectedAtom(SelectedAtomicTerm(SelectedAtomicTermUF(cl, i, j))); });
    //              },
    //
    //
    //              /* literals  (~)P(t1 ... tn)  */
    //              [&]() { return iterItems(SelectedAtom(SelectedAtomicLiteral(cl, i))); }
    //          );
    //        });
    // }
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
