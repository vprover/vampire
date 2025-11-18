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
 * @file Monotonicity.hpp
 * Code for computing whether a sort is monotonic 
 *
 * @since 6/01/2016 Manchester
 * @author Giles
 */

#ifndef __Monotonicity__
#define __Monotonicity__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"

#include "SAT/SATSolver.hpp"
#include "SAT/SATLiteral.hpp"

namespace FMB {
  using namespace Kernel;
  using namespace SAT;
  using namespace Lib;

class Monotonicity{
public:
  // Assumes clauses are flattened
  Monotonicity(ClauseList* clauses, unsigned srt);

  /**
   * Returns nullptr if not monotone.
   *
   * If the answer is positive, it will allocate a DArray to store
   * for every predicate symbol whether it should be treated (in sort srt)
   * as false-extended (-1), copy-extended (0), or true-extended (+1).
   */
  DArray<signed char>* check();

  static void addSortPredicates(bool withMon, ClauseList*& clauses, const DArray<bool>& del_f,
    DHMap<unsigned,DArray<signed char>*>& monotonic_vampire_sorts, Stack<unsigned>& sort_predicates);
  static void addSortFunctions(bool withMon, ClauseList*& clauses,
    DHMap<unsigned,DArray<signed char>*>& monotonic_vampire_sorts, Stack<unsigned>& sort_functions);

private:
  void monotone(Clause* c, Literal* l);

  void safe(Clause* c, Literal* l, TermList* t);
  void safe(Clause* c, Literal* l, TermList* t, SATLiteral add);
  void safe(Clause* c, Literal* l, TermList* t, Stack<SATLiteral>& slits);

  // returns true if the true literal should be added to slits
  // returns false otherwise (if false should be added or something else has been added)
  bool guards(Literal* l, unsigned var, Stack<SATLiteral>& slits);

  unsigned _srt;

  // the constructor computes the result
  bool _result;

  DHMap<unsigned,SATLiteral> _pF;
  DHMap<unsigned,SATLiteral> _pT;

  ScopedPtr<SATSolver> _solver;
};

}
#endif
