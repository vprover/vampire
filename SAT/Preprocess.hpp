/**
 * @file Preprocessor.hpp
 * Defines class Preprocessor.
 */


#ifndef __SATPreprocess__
#define __SATPreprocess__

#include "../Lib/VirtualIterator.hpp"

#include "SATClause.hpp"

namespace SAT {

class Preprocess
{
public:
  static SATClauseIterator propagateUnits(unsigned varCnt, SATClauseIterator clauses);
  static SATClauseIterator randomizeVariables(unsigned varCnt, SATClauseIterator clauses);
  static SATClauseIterator reorderVariablesByResolvability(unsigned varCnt, SATClauseIterator clauses);
  static SATClauseIterator reorderVariablesByConflicts(unsigned varCnt, SATClauseIterator clauses,
	  unsigned* conflictCnts);
  static SATClauseIterator removeDuplicateLiterals(SATClauseIterator clauses);
protected:
  static void createVarProfile(unsigned var, DArray<unsigned>& profile, DArray<SATClauseList*>& clsByVar,
      Set<unsigned>& fixed);

  static SATClauseIterator permutateVariables(unsigned varCnt, SATClauseIterator clauses,
	  unsigned* permutation);
};

};

#endif /* __SATPreprocess__ */
