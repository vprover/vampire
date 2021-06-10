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

  // shuffling should not require allocating new memory, so all the objects are modified "in place"

  void shuffle(Unit*);     // shuffle a unit; just dispatches to either shuffle(Clause*) or shuffle(Formula*)
  void shuffle(Clause*);   // shuffling a clause; it assumes literals are shared (i.e. nothing "special" in them anyway) so it does not touch those
  void shuffle(Formula*);  // shuffling a formula; will try to descend also to the term level, to shuffle around commutative operators and formulas inside terms (if applicable)
  void shuffle(Literal*);
  void shuffle(TermList);

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

  // list2 is assumed to be of the same length as list1; they are suffled "in sync"
  template<typename T, typename S>
  void shuffleTwoList(List<T>*& list1, List<S>*& list2) {
    CALL("Shuffling::shuffleTwoList");

    unsigned len = List<T>::length(list1);

    if (len <= 1) {
      return;
    }

    DArray<std::pair<List<T>*,List<S>*>> aux(len);
    unsigned idx = 0;

    List<T>* els1 = list1;
    List<S>* els2 = list2;
    while (els1 != nullptr) {
      ASS_NEQ(els2,0);
      aux[idx++] = std::make_pair(els1,els2);
      els1 = els1->tail();
      els2 = els2->tail();
    }
    ASS_EQ(els2,0);
    shuffleArray(aux,len);

    // reconnect the links
    len--; // we need a special handling of the last element (and also a one smaller condition)
    aux[len].first->setTail(nullptr);
    aux[len].second->setTail(nullptr);
    for(idx = 0; idx < len; idx++) {
      aux[idx].first->setTail(aux[idx+1].first);
      aux[idx].second->setTail(aux[idx+1].second);
    }

    list1 = aux[0].first;
    list2 = aux[0].second;
  }

private:



}; // class Shuffling

}

#endif
