
/*
 * File CheckedSatSolver.cpp.
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

void CheckedSatSolver::ensureVarCount(unsigned newVarCnt)
{
  CALL("CheckedSatSolver::ensureVarCnt");

  _varCnt = std::max(_varCnt, newVarCnt);
  _inner->ensureVarCount(newVarCnt);
}

void CheckedSatSolver::addClause(SATClause* cl)
{
  CALL("CheckedSatSolver::addClause");
  ASS(_inner);

  _clauses.push(cl);
  _inner->addClause(cl);
  _checked = false;
}

void CheckedSatSolver::addClauseIgnoredInPartialModel(SATClause* cl)
{
  CALL("CheckedSatSolver::addClauseIgnoredInPartialModel");

  // It is a bit ugly to ignore these clauses for checking
  // but we need to be less strict for the case when checking a minimizing solver 
  
  // TODO: consider checking that the returned partial model
  // can be extended to a full model that satisfies even these clauses
  
  _inner->addClauseIgnoredInPartialModel(cl);
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
  ASS_G(var,0); ASS_LE(var,_varCnt);

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
