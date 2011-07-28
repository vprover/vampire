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
  static unsigned getResultSort(Term* t);
  static unsigned getArgSort(Term* t, unsigned argIndex);

  static unsigned getEqualityArgumentSort(const Literal* lit);

  static bool tryGetVariableSort(unsigned var, Formula* f, unsigned& res);
  static unsigned getVariableSort(TermList var, Term* t);
  static unsigned getTermSort(TermList trm, Literal* lit);

  static void collectVariableSorts(Unit* u, DHMap<unsigned,unsigned>& map);
  static void collectVariableSorts(Term* t, DHMap<unsigned,unsigned>& map);
  static void collectVariableSorts(Formula* f, DHMap<unsigned,unsigned>& map);

  static bool areSortsValid(Clause* cl);

  static BaseType& getType(Term* t);
private:
  static bool tryGetVariableSort(TermList var, Term* t, unsigned& result);

  static bool areSortsValid(Term* t, DHMap<unsigned,unsigned>& varSorts);
};

}

#endif // __SortHelper__
