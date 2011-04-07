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

  static unsigned getEqualityArgumentSort(Literal* lit);

  static unsigned getVariableSort(TermList var, Term* t);
  static unsigned getTermSort(TermList trm, Literal* lit);

  static bool areSortsValid(Clause* cl);

  static BaseType& getType(Term* t);
private:
  static bool tryGetVariableSort(TermList var, Term* t, unsigned& result);

  static bool areSortsValid(Term* t, DHMap<TermList,unsigned>& varSorts);
};

}

#endif // __SortHelper__
