/**
 * @file CheckedSatSolver.cpp
 * Implements class CheckedSatSolver.
 */

#include "Lib/Exception.hpp"

#include "CheckedSatSolver.hpp"

namespace Test
{

CheckedSatSolver::CheckedSatSolver(SATSolver* inner)
 : _inner(inner),
   _checked(false),
   _varCnt(0)
{
  CALL("CheckedSatSolver::CheckedSatSolver");
}

void CheckedSatSolver::ensureVarCnt(unsigned newVarCnt)
{
  CALL("CheckedSatSolver::ensureVarCnt");

  _varCnt = std::max(_varCnt, newVarCnt);
  _inner->ensureVarCnt(newVarCnt);
}

void CheckedSatSolver::addClauses(SATClauseIterator cit)
{
  CALL("CheckedSatSolver::addClauses");

  static SATClauseStack newClauses;
  newClauses.reset();
  newClauses.loadFromIterator(cit);
  
  _clauses.loadFromIterator(SATClauseStack::BottomFirstIterator(newClauses));

  _inner->addClauses(pvi(SATClauseStack::BottomFirstIterator(newClauses)));
  _checked = false;
}

void CheckedSatSolver::addClausesIgnoredInPartialModel(SATClauseIterator cit)
{
  CALL("CheckedSatSolver::addClausesIgnoredInPartialModel");

  // It is a bit ugly to ignore these clauses for checking
  // but we need to be less strict for the case when checking a minimizing solver 
  
  // TODO: consider checking that the returned partial model
  // can be extended to a full model that satisfies even these clauses
  
  _inner->addClauses(cit);
  _checked = false;  
}

SATSolver::Status CheckedSatSolver::solve(unsigned conflictCountLimit)
{
  CALL("CheckedSatSolver::solve");
  
  _checked = false;
  return _inner->solve(conflictCountLimit);
}

SATSolver::VarAssignment CheckedSatSolver::getAssignment(unsigned var)
{
  CALL("CheckedSatSolver::getAssignment");
  //ASS_EQ(_inner->getStatus(), SATISFIABLE);

  ensureChecked();
  return _inner->getAssignment(var);
}

bool CheckedSatSolver::isSatisfied(SATClause* cl)
{
  CALL("CheckedSatSolver::isSatisfied");

  SATClause::Iterator it(*cl);
  while(it.hasNext()) {
    SATLiteral l = it.next();
    if(_inner->trueInAssignment(l)) {
      return true;
    }
  }
  return false;
}

void CheckedSatSolver::doCheck()
{
  CALL("CheckedSatSolver::doCheck");

  SATClauseStack::Iterator cit(_clauses);
  while(cit.hasNext()) {
    SATClause* cl = cit.next();
    if(!isSatisfied(cl)) {
      ASS_REP2(false, "reported satisfiable assignment which does not satisfy all clauses", *cl);
      INVALID_OPERATION("reported satisfiable assignment which does not satisfy all clauses");
    }
  }
}

/*
void CheckedSatSolver::addAssumption(SATLiteral lit, unsigned conflictCountLimit)
{
  CALL("CheckedSatSolver::addAssumption");

  _assumptions.insert(lit.var(), lit.polarity());
  _checked = false;
  _inner->addAssumption(lit, conflictCountLimit);
}

void CheckedSatSolver::retractAllAssumptions()
{
  CALL("CheckedSatSolver::retractAllAssumptions");

  _assumptions.reset();
  _checked = false;
  _inner->retractAllAssumptions();
}
*/

}
