/**
 * @file SortHelper.hpp
 * Defines class SortHelper.
 */

#ifndef __SortHelper__
#define __SortHelper__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Term.hpp"

namespace Kernel {

class SortHelper {
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

  static BaseType& getType(Term* t);

  static bool areSortsValid(Term* t, DHMap<unsigned,unsigned>& varSorts);
private:
  // It is important this function is private, because it only works in cooperation with tryGetVariableSort(unsigned var, Formula* f, unsigned& res);
  static bool tryGetVariableSort(TermList var, Term* t, unsigned& result);

};

}

#endif // __SortHelper__
