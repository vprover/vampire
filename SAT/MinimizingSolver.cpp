/**
 * @file MinimizingSolver.cpp
 * Implements class MinimizingSolver.
 */

#include "MinimizingSolver.hpp"

namespace SAT
{

MinimizingSolver::MinimizingSolver(SATSolver* inner)
 : _inner(inner),
   _assignmentValid(false)
{
  CALL("MinimizingSolver::MinimizingSolver");

  _assignmentValid = false;
}

void MinimizingSolver::ensureVarCnt(unsigned newVarCnt)
{
  CALL("MinimizingSolver::ensureVarCnt");

  _inner->ensureVarCnt(newVarCnt);
  _asgn.expand(newVarCnt);
  _watcher.expand(newVarCnt);
  _assignmentValid = false;
}

void MinimizingSolver::addClauses(SATClauseIterator cit, bool onlyPropagate)
{
  CALL("MinimizingSolver::addClauses");

  static SATClauseStack newClauses;
  newClauses.reset();
  newClauses.loadFromIterator(cit);
  _unprocessed.loadFromIterator(SATClauseStack::BottomFirstIterator(newClauses));

  _inner->addClauses(pvi(SATClauseStack::BottomFirstIterator(newClauses)), onlyPropagate);
  _assignmentValid = false;
}

SATSolver::VarAssignment MinimizingSolver::getAssignment(unsigned var)
{
  CALL("MinimizingSolver::getAssignment");
  ASS_EQ(_inner->getStatus(), SATISFIABLE);

  if(!_assignmentValid) {
    updateAssignment();
  }

  if(!_assumptions.isEmpty() && _assumptions.find(var)) {
    return _assumptions.get(var) ? SATSolver::TRUE : SATSolver::FALSE;
  }

  if(_watcher[var].isEmpty()) {
    return SATSolver::DONT_CARE;
  }
  return _asgn[var] ? SATSolver::TRUE : SATSolver::FALSE;
}

void MinimizingSolver::updateAssignment()
{
  CALL("MinimizingSolver::updateAssignment");

  NOT_IMPLEMENTED;
}


void MinimizingSolver::addAssumption(SATLiteral lit, bool onlyPropagate)
{
  CALL("MinimizingSolver::addAssumption");

  _assumptions.insert(lit.var(), lit.polarity());
  _inner->addAssumption(lit, onlyPropagate);
  _assignmentValid = false;
}

void MinimizingSolver::retractAllAssumptions()
{
  CALL("MinimizingSolver::retractAllAssumptions");

  _assumptions.reset();
  _inner->retractAllAssumptions();
}


}
