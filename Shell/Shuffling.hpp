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
 * @file Shuffling.hpp
 * Defines class Shuffling implementing the shuffling of the input.
 * @since 9/6/2021 Prague
 */

#ifndef __Shuffling__
#define __Shuffling__

#include "Forwards.hpp"

#include "Lib/List.hpp"
#include "Kernel/Unit.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * Class implementing shuffling-related procedures.
 * @since 09/06/2021 Prague
 */
class Shuffling
{
public:
  void shuffle(Problem&);
  void shuffle(UnitList*&);

  void shuffle(Unit*);     // shuffle a unit; just dispatches to either shuffle(Clause*) or shuffle(Formula*)
  void shuffle(Clause*);   // shuffling a clause; it assumes literals are shared (i.e. nothing "special" in them anyway) so it does not touch those
  void shuffle(Formula*);  // shuffling a formula; will try to descend also to the term level, to shuffle around commutative operators and formulas inside terms (if applicable)

  template<typename Arrayish>
  void shuffleArray(Arrayish& a, unsigned len) {
    CALL("Shuffling::shuffleArray");

    for(unsigned i=0;i<len;i++){
      unsigned j = Random::getInteger(len-i)+i;
      std::swap(a[i],a[j]);
    }
  }

  // destructive shuffle of a list using an auxiliary array
  template<typename T>
  void shuffleList(List<T>*& list) {
    CALL("Shuffling::shuffleList");

    unsigned len = List<T>::length(list);

    if (len <= 1) {
      return;
    }

    DArray<List<T>*> aux(len);
    unsigned idx = 0;

    List<T>* els = list;
    while (els != nullptr) {
      aux[idx++] = els;
      els = els->tail();
    }
    shuffleArray(aux,len);

    // reconnect the links
    len--; // we need a special handling of the last element (and also a one smaller condition)
    aux[len]->setTail(nullptr);
    for(idx = 0; idx < len; idx++) {
      aux[idx]->setTail(aux[idx+1]);
    }

    list = aux[0];
  }

}; // class Shuffling

}

#endif
