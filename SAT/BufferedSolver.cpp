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
 : _allOnlyPropagate(true), _inner(inner), _maxVar(0)
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
 * TODO - use a map of alternatives to attempt to change the value
 *        in the buffer for a new literal
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
    if(l.var() > _maxVar) newLiterals.push(l); 
  }
  // if we get to here then the clause is not currently implied
  // by the ground model or literalBuffer

  //now go through and try and make a new literal true
  SATLiteralStack::Iterator newLitsIt(newLiterals);
  while(newLitsIt.hasNext()){
    SATLiteral l = newLitsIt.next();
    if(!_literalBuffer.find(l.var())){
      _literalBuffer.insert(l.var(),l.polarity());
      //TODO update alternatives
      return true;
    }
  }
  // if we get to here then all new literals are set to the
  // opposite of desired. 

  //now try alternatives for set new literals
  //TODO

  return false;
}

/**
 * Add clauses to sat solver
 *
 * If all clauses are implied we add them to buffer, but if any are not we must
 * flush all unadded clauses.
 *
 * @author Giles
 */
void BufferedSolver::addClauses(SATClauseIterator cit, bool onlyPropagate)
{
  CALL("BufferedSolver::addClauses");

  static SATClauseStack newClauses;
  newClauses.reset();
  newClauses.loadFromIterator(cit);

  // add clauses to _unadded
  _unadded.loadFromIterator(SATClauseStack::BottomFirstIterator(newClauses));

  // check if clauses are implied by current ground model and bufferd literals
  bool all_implied = true;
  SATClauseStack::Iterator newIt(newClauses);
  while(newIt.hasNext()){
    SATClause* cl = newIt.next();
    if(!checkAndRecordImplied(cl)){
      all_implied=false;
      RSTAT_CTR_INC("solver_buffer_miss");
      break;
    }
  }

  //record onlyPropagate value
  _allOnlyPropagate &= onlyPropagate;

  // if there are any not implied clauses then flush all unadded to inner 
  if(!all_implied) flushUnadded();
  else RSTAT_CTR_INC("solver_buffer_hit");

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
  _maxVar=_tmaxVar;

  // flush _unadded to _inner
  _inner->addClauses(pvi(SATClauseStack::BottomFirstIterator(_unadded)),_allOnlyPropagate);

  // reset
  _unadded.reset();
  _literalBuffer.reset();
  //_alternatives.reset();
  _allOnlyPropagate=true;
}

/**
 * To get the assignment for a variable we first check the buffer
 * and then set of assumptions.
 *
 * If a variable is not in the sat solver we return DONT_CARE
 *
 * @author Giles
 */
SATSolver::VarAssignment BufferedSolver::getAssignment(unsigned var)
{
  CALL("BufferedSolver::getAssignment");

  // check buffer
  if(!_literalBuffer.isEmpty() && _literalBuffer.find(var)) {
    return _literalBuffer.get(var) ? SATSolver::TRUE : SATSolver::FALSE;
  }
  // check assumptions
  if(!_assumptions.isEmpty() && _assumptions.find(var)) {
    return _assumptions.get(var) ? SATSolver::TRUE : SATSolver::FALSE;
  }

  // refer to inner if variable not new
  if(var < _maxVar){
    return _inner->getAssignment(var); 
  }
  else{
   return SATSolver::DONT_CARE; // If it is new and not yet assigned in buffer
  }
}


/**
 * Add an assumption if it is not already implied
 *
 * @author Giles
 */
void BufferedSolver::addAssumption(SATLiteral lit, unsigned conflictCountLimit)
{
  CALL("BufferedSolver::addAssumption");

  _assumptions.insert(lit.var(), lit.polarity());

  // only add assumption if it is not already satisfied
  // note that trueInAssignment will query buffer also
  if(!trueInAssignment(lit)){
  	_inner->addAssumption(lit, conflictCountLimit);
  }
}

/**
 *
 * Retract all assumptions. This requires flushing as some buffered clauses
 * may rely on assumptions.
 *
 * @author Giles
 */
void BufferedSolver::retractAllAssumptions()
{
  CALL("BufferedSolver::retractAllAssumptions");
  // only need to retract if there are any
  if(!_assumptions.isEmpty()){
    _inner->retractAllAssumptions();
    _assumptions.reset();
    //also need to flush the buffer as they may rely on assumptions
    //TODO - we could track which unadded clauses rely on assumptions,
    // but it is unlikely to be many
    flushUnadded();
  }
}


}
