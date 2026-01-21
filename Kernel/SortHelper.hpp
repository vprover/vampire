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
 * @file SortHelper.hpp
 * Defines class SortHelper.
 */

#ifndef __SortHelper__
#define __SortHelper__

#include "Forwards.hpp"

namespace Kernel {

class SortHelper {
public:
  static TermList getResultSort(const Term* t);
  static TermList getResultSortMono(const Term* t);
  static TermList getResultSort(TermList t, DHMap<unsigned,TermList>& varSorts);
  static TermList getArgSort(Term const* t, unsigned argIndex);
  static TermList getTermArgSort(Term const* t, unsigned argIndex);

  static bool tryGetResultSort(const Term* t, TermList& result);
  static bool tryGetResultSort(const TermList t, TermList& result);
  static bool getResultSortOrMasterVariable(const Term* t, TermList& resultSort, TermList& resultVar);
  static bool getResultSortOrMasterVariable(const TermList t, TermList& resultSort, TermList& resultVar);

  static TermList getEqualityArgumentSort(const Literal* lit);

  // DEPRECATED: this function scans the whole formula to figure out a variable's sort and is very inefficient - moreover, such information is normally carried around (see QuantifiedFormula's sorts())
  static bool tryGetVariableSort(unsigned var, Formula* f, TermList& res);
  static TermList getVariableSort(TermList var, Term* t);

  static void collectVariableSorts(Unit* u, DHMap<unsigned,TermList>& map);
  static void collectVariableSorts(Term* t, DHMap<unsigned,TermList>& map);
  static void collectVariableSorts(Formula* f, DHMap<unsigned,TermList>& map, bool ignoreBound = false);

  static bool areImmediateSortsValidPoly(Term* t);
  static bool areImmediateSortsValidMono(Term* t);
  static bool allTopLevelArgsAreSorts(AtomicSort* sort);

  static TermList getIndexSort(TermList arraySort);
  static TermList getInnerSort(TermList arraySort);

  static void normaliseArgSorts(VList* qVars, TermStack& argSorts);
  static void normaliseSort(VList* qVars, TermList& sort);
  static void normaliseArgSorts(const TermStack& qVars, TermStack& argSorts);
  static void normaliseSort(TermStack qVars, TermList& sort);

  /**
   * This function achieves the following. Let t = f<a1, a2>(t1, t2)
   * where ai are type arguments and ti are terms arguments. Let f have
   * type !>[X, Y]: (s1 * s2) > s3. The function returns the substitution
   * \sigma = [X -> a1, Y -> a2]. The type of t is s3\sigma, the type of
   * t1 s1\sigma and the type of t2 s2\sigma
   *
   * The function returns true, if all the replacement terms in the substitution
   * are shared.
   *
   * @author Ahmed Bhayat
   */
  static bool getTypeSub(const Term *t, Substitution &subst);

  static bool areSortsValid(Clause* cl);
  static bool areSortsValid(Term* t);
  static bool areSortsValid(Term* t, DHMap<unsigned,TermList>& varSorts);
private:
  static bool tryGetVariableSortTerm(TermList var, Term* t, TermList& result, bool recurseToSubformulas);
};

}

#endif // __SortHelper__
