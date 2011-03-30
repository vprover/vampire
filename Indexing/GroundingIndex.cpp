/**
 * @file GroundingIndex.cpp
 * Implements class GroundingIndex.
 */

#include "GroundingIndex.hpp"

#include "SAT/TWLSolver.hpp"

namespace Indexing
{

GroundingIndex::GroundingIndex()
{
  CALL("GroundingIndex::GroundingIndex");

  _solver = new TWLSolver();
}

void GroundingIndex::handleClause(Clause* c, bool adding)
{
  CALL("GroundingIndex::handleClause");

  if(!adding) {
    //We do not remove clauses from the SAT solver.
    return;
  }
  if(c->splits() && c->splits()->size()!=0) {
    //Since we don't remove clauses, we must ignore clauses with splitting
    //history, because it wouldn't be possible to backtrack them
    return;
  }
}

}
