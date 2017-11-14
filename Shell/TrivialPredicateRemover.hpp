
/*
 * File TrivialPredicateRemover.hpp.
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
 * @file TrivialPredicateRemover.hpp
 * Defines class TrivialPredicateRemover.
 */

#ifndef __TrivialPredicateRemover__
#define __TrivialPredicateRemover__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Set.hpp"



namespace Shell {

using namespace Kernel;

class TrivialPredicateRemover {
public:
  TrivialPredicateRemover();

  void apply(Problem& prb);
  bool apply(UnitList*& units);

private:
  void scan(UnitList* units);
  void count(Clause* cl, int add);

  /** Number of clauses in which predicate occurs only positively */
  DArray<int> _posOcc;
  /** Number of clauses in which predicate occurs only negatively */
  DArray<int> _negOcc;

  typedef Set<Clause*> ClauseSet;

  DArray<ClauseSet> _predClauses;

  Stack<unsigned> _reachedZeroes;

  ClauseSet _removed;

  Problem* _processedProblem;
};

}

#endif // __TrivialPredicateRemover__
