
/*
 * File Preprocess.hpp.
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
 * @file SAT/Preprocess.hpp
 * Defines class Preprocess.
 */


#ifndef __SATPreprocess__
#define __SATPreprocess__

#include "Forwards.hpp"

#include "Lib/VirtualIterator.hpp"

#include "SATClause.hpp"

namespace SAT {

class Preprocess
{
public:
  static SATClauseIterator filterPureLiterals(unsigned varCnt, SATClauseIterator clauses);
  static bool filterPureLiterals(unsigned varCnt, SATClauseList*& clauses);

  static void propagateUnits(SATClauseIterator clauses,
  	SATClauseIterator& resUnits, SATClauseIterator& resNonUnits);

  /* UNUSED; moreover, not compatible with the convetion that variables start from 1
  static SATClauseIterator randomizeVariables(unsigned varCnt, SATClauseIterator clauses);
  static SATClauseIterator reorderVariablesByResolvability(unsigned varCnt, SATClauseIterator clauses);
  static SATClauseIterator reorderVariablesByConflicts(unsigned varCnt, SATClauseIterator clauses,
	  unsigned* conflictCnts);
	  */
  static SATClause* removeDuplicateLiterals(SATClause* cl);
  static SATClauseIterator removeDuplicateLiterals(SATClauseIterator clauses);

  static SATClauseIterator generate(unsigned literalsPerClause,
	  unsigned varCnt, float clausesPerVariable);

protected:
  static void createVarProfile(unsigned var, DArray<unsigned>& profile, DArray<SATClauseList*>& clsByVar,
      Set<unsigned>& fixed);
  static SATClauseIterator permutateVariables(unsigned varCnt, SATClauseIterator clauses,
	  unsigned* permutation);
};

};

#endif /* __SATPreprocess__ */
