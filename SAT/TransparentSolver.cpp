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
  SATClause::Iterator it1(cl);
  while(it1.hasNext()) {
    SATLiteral lit = it1.next();
    if(trySweepPure(lit.var()), false) {
      ALWAYS(tryWatchOrSubsume(cl));
      return;
    }
  }
}

/**
 * @param eager if false, we return false after the first failure
 *        to move a clause elsewhere
 */
bool TransparentSolver::trySweepPure(unsigned var, bool eager)
{
  CALL("TransparentSolver::trySweepPure");

  VarInfo& vi = _vars[var];
  SATClauseStack::Iterator wit(vi._watched);
  while(wit.hasNext()) {
    SATClause* cl = wit.next();
#if VDEBUG
    size_t wstackSize = vi._watched.size();
#endif
    bool wasMovedOut = tryWatchOrSubsume(cl, var);
    ASS_EQ(wstackSize, vi._watched.size()); //we assert we didn't put the watched clause here
    if(wasMovedOut) {
      wit.del();
    } else if(!eager) {
      return false;
    }
  }
  if(vi._watched.isEmpty()) {
    vi._pureInitialized = false;
    return true;
  }
  return false;
}

/**
 * Return true if clause was watched at some pure variable or subsumed.
 *
 * If forbiddenVar is non-zero,
 */
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
