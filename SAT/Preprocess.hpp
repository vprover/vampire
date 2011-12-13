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
  static SATClauseIterator randomizeVariables(unsigned varCnt, SATClauseIterator clauses);
  static SATClauseIterator reorderVariablesByResolvability(unsigned varCnt, SATClauseIterator clauses);
  static SATClauseIterator reorderVariablesByConflicts(unsigned varCnt, SATClauseIterator clauses,
	  unsigned* conflictCnts);
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
