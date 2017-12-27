
/*
 * File SortHelper.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file SortHelper.hpp
 * Defines class SortHelper.
 */

#ifndef __SortHelper__
#define __SortHelper__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/Term.hpp"

namespace Kernel {

class SortHelper {
private:
  enum CollectWhat {
    COLLECT_TERM,
    COLLECT_TERMLIST,
    COLLECT_SPECIALTERM,
    COLLECT_FORMULA
  };

  struct CollectTask {
    CollectWhat fncTag;
    union {
      Term* t; // shared by TERM and SPECIALTERM
      Formula* f;
    };
    TermList ts; // outside of union, because it has a non-trivial constructor
    unsigned contextSort; // only used by TERMLIST and SPECIALTERM
  };

  static void collectVariableSortsIter(CollectTask task, DHMap<unsigned,unsigned>& map);
public:
  static unsigned getResultSort(const Term* t);
  static unsigned getResultSort(TermList t, DHMap<unsigned,unsigned>& varSorts);
  static unsigned getArgSort(Term* t, unsigned argIndex);

  static bool tryGetResultSort(const Term* t, unsigned& result);
  static bool tryGetResultSort(const TermList t, unsigned& result);
  static bool getResultSortOrMasterVariable(const Term* t, unsigned& resultSort, TermList& resultVar);
  static bool getResultSortOrMasterVariable(const TermList t, unsigned& resultSort, TermList& resultVar);

  static unsigned getEqualityArgumentSort(const Literal* lit);

  static bool tryGetVariableSort(unsigned var, Formula* f, unsigned& res);
  static unsigned getVariableSort(TermList var, Term* t);
  static unsigned getTermSort(TermList trm, Literal* lit);

  static void collectVariableSorts(Unit* u, DHMap<unsigned,unsigned>& map);
  static void collectVariableSorts(Term* t, DHMap<unsigned,unsigned>& map);
  static void collectVariableSorts(TermList ts, unsigned contextSort, DHMap<unsigned,unsigned>& map);
  static void collectVariableSortsSpecialTerm(Term* t, unsigned contextSort, DHMap<unsigned,unsigned>& map);
  static void collectVariableSorts(Formula* f, DHMap<unsigned,unsigned>& map);

  static bool areSortsValid(Clause* cl);
  static bool areImmediateSortsValid(Term* t);

  static OperatorType& getType(Term* t);

  static bool areSortsValid(Term* t, DHMap<unsigned,unsigned>& varSorts);
private:
  // It is important this function is private, because it only works in cooperation with tryGetVariableSort(unsigned var, Formula* f, unsigned& res);
  static bool tryGetVariableSort(TermList var, Term* t, unsigned& result);

};

}

#endif // __SortHelper__
