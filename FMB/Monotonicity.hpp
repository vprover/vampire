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

#include "Lib/Stack.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"

#include "SAT/SATSolver.hpp"
#include "SAT/SATLiteral.hpp"
#include "SAT/SATClause.hpp"

#include "Lib/Allocator.hpp"

namespace FMB {
  using namespace Kernel;
  using namespace SAT;
  using namespace Lib;

class Monotonicity{

  CLASS_NAME(Monotonicity);
  USE_ALLOCATOR(Monotonicity);

public:
  // Assumes clauses are flattened
  Monotonicity(ClauseList* clauses, unsigned srt);

  bool check(){ return _result;}

  static void addSortPredicates(bool withMon, ClauseList*& clauses, DArray<unsigned>& del_f);
  static void addSortFunctions(bool withMon, ClauseList*& clauses);

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
