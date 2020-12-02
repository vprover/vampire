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
 * @file BufferedSolver.cpp
 * Implements class BufferedSolver.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "SAT/SATClause.hpp"

#include "BufferedSolver.hpp"

namespace SAT
{

BufferedSolver::BufferedSolver(SATSolver* inner)
 : _inner(inner), _checkedIdx(0), _lastStatus(SATISFIABLE), _varCnt(0), _varCntInnerOld(0)
{
  CALL("BufferedSolver::BufferedSolver");
}
/**
 * Check if cl is implied by the current model i.e. if a literal
 * - is already true in the model
 * - is new and can be assumed true
 *
 * We record the assumptions about new literals, if a later clause
 * occurs with a contradicting value for a new literal we currently
 * flag a conflict and flush everything.
 *
 * @author Giles
 */
bool BufferedSolver::checkAndRecordImplied(SATClause* cl)
{
  CALL("BufferedSolver::checkAndRecordImplied");

  static SATLiteralStack newLiterals;
  newLiterals.reset();

  for(unsigned lIndex=0;lIndex<cl->length();lIndex++)
  {
    SATLiteral l = (*cl)[lIndex];
    // check if l is already implied, if so the clause is implied and we can stop
    // note that trueInAssignment calls this version of getAssignment, which queries the buffer
    if(trueInAssignment(l)) return true;

    // record if l is new
    if(l.var() > _varCntInnerOld) newLiterals.push(l);
  }
  // if we get to here then the clause is not currently implied
  // by the ground model or literalBuffer

  //now go through and try and make a new literal true
  SATLiteralStack::Iterator newLitsIt(newLiterals);
  while(newLitsIt.hasNext()){
    SATLiteral l = newLitsIt.next();
    if(!_literalBuffer.find(l.var())){
      _literalBuffer.insert(l.var(),l.polarity());
      return true;
    }
  }
  // if we get to here then all new literals are set to the
  // opposite of desired. 

  return false;
}

/**
 * Add a clause to sat solver
 *
 * @author Giles, Martin
 */
void BufferedSolver::addClause(SATClause* cl)
{
  CALL("BufferedSolver::addClause");

  _unadded.push(cl);
}

/**
 * Any new variables that have not been added to the inner SAT solver
 * are added.
 *
 * Called when an added clause cannot be made true.
 *
 * @author Giles
 * @since 14/03/2014
 */
void BufferedSolver::flushUnadded()
{
  CALL("BufferedSolver::flushUnadded");

  //update maxVar
  _varCntInnerOld=_varCnt;

  // flush _unadded to _inner
  _inner->addClausesIter(pvi(SATClauseStack::BottomFirstIterator(_unadded)));

  // reset
  _unadded.reset();
  _checkedIdx = 0;
  _literalBuffer.reset();
}

/**
 * Check unadded clauses.
 * 
 * If all are implied we add keep them in buffer, 
 * but if any are not we must flush all unadded clauses.
 *
 * @author Martin
 */
SATSolver::Status BufferedSolver::solve(unsigned conflictCountLimit)
{
  CALL("BufferedSolver::solve"); 
  
  // BufferedSolver does not support "UNKNOWN" status as
  // it needs _inner to have either a model or to be provably unsat
  ASS_EQ(conflictCountLimit, UINT_MAX);
  
  if (_lastStatus == UNSATISFIABLE) {
    return UNSATISFIABLE;
  }
  
  ASS_EQ(_lastStatus,SATISFIABLE);
  
  // check if clauses are implied by current ground model and buffered literals
  size_t sz = _unadded.size();
  while(_checkedIdx < sz){
    SATClause* cl = _unadded[_checkedIdx++];
    if(!checkAndRecordImplied(cl)){
      RSTAT_CTR_INC("solver_buffer_miss");
      flushUnadded();
      return (_lastStatus = _inner->solve(conflictCountLimit));
    }
  }

  RSTAT_CTR_INC("solver_buffer_hit");
  return SATSolver::SATISFIABLE;
}

/**
 * To get the assignment for a variable we first check the buffer.
 * If a variable is not in the sat solver we return DONT_CARE
 *
 * @author Giles
 */
SATSolver::VarAssignment BufferedSolver::getAssignment(unsigned var)
{
  CALL("BufferedSolver::getAssignment");
  ASS_G(var,0); ASS_LE(var,_varCnt);

  // check buffer
  if(!_literalBuffer.isEmpty() && _literalBuffer.find(var)) {
    return _literalBuffer.get(var) ? SATSolver::TRUE : SATSolver::FALSE;
  }

  // refer to inner if variable not new
  if (var <= _varCntInnerOld) {
    return _inner->getAssignment(var); 
  } else {
    return SATSolver::DONT_CARE; // If it is new and not yet assigned in buffer
  }
}

}
