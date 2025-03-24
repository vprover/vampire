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
namespace Kernel {
  class AlascaSelector {

    // TODO make an array class that doesn't have any capacity slack
    Map<Clause* , Stack<NewSelectedAtom>> _cache;
    Stack<NewSelectedAtom> computeSelected(Stack<NewSelectedAtom> atoms, Ordering* ord);
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
    //                       .map([cl,i](auto s_i) -> NewSelectedAtom {
    //                           return  NewSelectedAtom(SelectedAtomicTerm(SelectedAtomicTermItp<decltype(itp.numTraits())>(
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
    //                   .map([cl,i](auto j) { return NewSelectedAtom(SelectedAtomicTerm(SelectedAtomicTermUF(cl, i, j))); });
    //              },
    //
    //
    //              /* literals  (~)P(t1 ... tn)  */
    //              [&]() { return iterItems(NewSelectedAtom(SelectedAtomicLiteral(cl, i))); }
    //          );
    //        });
    // }
  public:
    auto selected(Clause* cl, Ordering* ord)
    {
      return arrayIter(_cache.getOrInit(cl, [&]() {
            return computeSelected(NewSelectedAtom::iter(cl).collectStack(), ord);
      }));
    }
  };
};

#endif
