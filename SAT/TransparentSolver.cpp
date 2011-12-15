/**
 * @file TransparentSolver.cpp
 * Implements class TransparentSolver.
 */

#include "TransparentSolver.hpp"

namespace SAT
{

void TransparentSolver::ensureVarCnt(unsigned newVarCnt)
{
  CALL("TransparentSolver::ensureVarCnt");

  _inner->ensureVarCnt(newVarCnt);
  _vars.expand(newVarCnt);
}

void TransparentSolver::addClauses(SATClauseIterator cit, bool onlyPropagate)
{
  CALL("TransparentSolver::addClauses");
  ASS(_toBeAdded.isEmpty());

  while(cit.hasNext()) {
    addClause(cit.next());
  }

  _inner->addClauses(pvi( SATClauseStack::Iterator(_toBeAdded) ), onlyPropagate);
}

void TransparentSolver::addClause(SATClause* cl)
{
  CALL("TransparentSolver::addClause");

  if(tryWatchOrSubsume(cl)) {
    return;
  }

}

bool TransparentSolver::trySweepPure(unsigned var)
{
  CALL("TransparentSolver::trySweepPure");

  VarInfo& vi = _vars[var];

}

///**
// * If wathed or subsumed, return 0, if simplified, return the simplified
// * clause, if nether was done, return the original clause.
// *
// * If clause is simplified and it contains an inference, inference
// * recording the simplification will be added to the new clause.
// */
bool TransparentSolver::tryWatchOrSubsume(SATClause* cl, unsigned forbiddenVar)
{
  CALL("TransparentSolver::tryWatchOrSubsume");

  SATClause::Iterator it(*cl);
  while(it.hasNext()) {
    SATLiteral lit = it.next();
    unsigned var = lit.var();
    if(var==forbiddenVar) {
      continue;
    }
    VarInfo& vi = _vars[var];
    if(vi._unit) {
      if(lit.polarity()==(*vi._unit)[0].polarity()) {
	//clause is subsumed by unit
	return true;
      }
    }
    if(!vi._pureInitialized) {
      vi._pureInitialized = true;
      vi._isPure = true;
      vi._isPurePositive = lit.polarity();
      vi._watched.push(cl);
      return true;
    }
    if(vi._isPure && vi._isPurePositive==lit.polarity()) {
      vi._watched.push(cl);
      return true;
    }
  }
  return false;
}

}
