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
#include "Lib/Coproduct.hpp"
#include "Kernel/Unit.hpp"

#include <algorithm>

namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * Class implementing shuffling-related procedures.
 * @since 09/06/2021 Prague
 */
class Shuffling
{
private:
  typedef Coproduct<Formula*, Literal*, TermList> Shufflable;

  static void shuffleIter(Shufflable sh);

public:
  static void polarityFlip(Problem&);

  static void shuffle(Problem&);
  static void shuffle(UnitList*&);

  // shuffling should not require allocating new memory, so all the objects are modified "in place"

  static void shuffle(Unit*);     // shuffle a unit; just dispatches to either shuffle(Clause*) or shuffle(Formula*)
  static void shuffle(Clause*);   // shuffling a clause; it assumes literals are shared (i.e. nothing "special" in them anyway) so it does not touch those

  static void shuffle(Formula* f) { shuffleIter(Shufflable(f)); }  // shuffling a formula; will try to descend also to the term level, to shuffle around commutative operators and formulas inside terms (if applicable)
  static void shuffle(Literal* l) { shuffleIter(Shufflable(l)); }
  static void shuffle(TermList tl) { shuffleIter(Shufflable(tl)); }

  template<typename Arrayish>
  // Implements Fisher–Yates shuffling (each permutation equally likely)
  static void shuffleArray(Arrayish& a, unsigned len) {
    CALL("Shuffling::shuffleArray");

    for(unsigned i=0;i<len;i++){
      unsigned j = Random::getInteger(len-i)+i;
      std::swap(a[i],a[j]);
    }
  }

  template<typename T>
  static void shuffleArray(T* ptr, unsigned len) { shuffleArray<T*&>(ptr, len); }

  // get a new list by shuffling the original
  // we leak the old one
  template<typename T>
  static void shuffleList(List<T>*& list) {
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

    // create the new list
    List<T>* res = nullptr;
    for(idx = 0; idx < len; idx++) {
      res = List<T>::cons(aux[idx]->head(),res);
    }

    // List<T>::destroy(list);
    list = res;
  }

  // list2 is assumed to be of the same length as list1;
  // get two new lists by shuffling the originals and leaking the old ones
  // they get shuffled "in sync"
  template<typename T, typename S>
  static void shuffleTwoList(List<T>*& list1, List<S>*& list2) {
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

    // create the new lists
    List<T>* res1 = nullptr;
    List<S>* res2 = nullptr;
    for(idx = 0; idx < len; idx++) {
      res1 = List<T>::cons(aux[idx].first->head(),res1);
      res2 = List<S>::cons(aux[idx].second->head(),res2);
    }

    // List<T>::destroy(list1);
    // List<S>::destroy(list2);

    list1 = res1;
    list2 = res2;
  }
}; // class Shuffling

}

#endif
