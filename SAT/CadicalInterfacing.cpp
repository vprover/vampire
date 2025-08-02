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
 * @file CadicalInterfacing.cpp
 * Implements class CadicalInterfacing
 */

#include "CadicalInterfacing.hpp"

namespace SAT
{

using namespace Shell;
using namespace Lib;

CadicalInterfacing::CadicalInterfacing(const Shell::Options& opts, bool generateProofs):
  _status(Status::SATISFIABLE)
{
  // these help a bit both for avataring and FMB
  _solver.set("phase",0);
  _solver.set("stabilizeonly",1);
}

Status CadicalInterfacing::solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit)
{
  // load assumptions:
  SATLiteralStack::ConstIterator it(assumps);
  _assumptions.clear();
  while (it.hasNext()) {
    _assumptions.push_back(vampire2Cadical(it.next()));
  }

  solveModuloAssumptionsAndSetStatus(conflictCountLimit);
  return _status;
}

SATLiteralStack CadicalInterfacing::failedAssumptions() {
  ASS_EQ(_status, Status::UNSATISFIABLE)

  SATLiteralStack result;
  for(int v : _assumptions)
    if(_solver.failed(v))
      result.push(cadical2Vampire(v).opposite());
  return result;
}

/**
 * Solve modulo assumptions and set status.
 * @b conflictCountLimit as with addAssumption.
 */
void CadicalInterfacing::solveModuloAssumptionsAndSetStatus(unsigned conflictCountLimit)
{
  _solver.limit("conflicts", conflictCountLimit);
  for(int assumption : _assumptions)
    _solver.assume(assumption);
  int res = _solver.solve();

  if (res == CaDiCaL::SATISFIABLE) {
    _status = Status::SATISFIABLE;
  } else if (res == CaDiCaL::UNSATISFIABLE) {
    _status = Status::UNSATISFIABLE;
  } else {
    _status = Status::UNKNOWN;
  }
}

/**
 * Add clause into the solver.
 *
 */
void CadicalInterfacing::addClause(SATClause* cl)
{
  // store to later generate the refutation
  PrimitiveProofRecordingSATSolver::addClause(cl);
  // TODO: consider measuring time
  ASS_EQ(_assumptions.size(),0);

  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++) {
    SATLiteral l = (*cl)[i];
    _solver.add(vampire2Cadical(l));
  }
  _solver.add(0);
}

/**
 * Perform solving and return status.
 */
Status CadicalInterfacing::solveLimited(unsigned conflictCountLimit)
{
  _assumptions.clear();
  solveModuloAssumptionsAndSetStatus(conflictCountLimit);
  return _status;
}

VarAssignment CadicalInterfacing::getAssignment(unsigned var)
{
  ASS_EQ(_status, Status::SATISFIABLE);
  ASS_G(var,0); ASS_L((int)var,_next);

  if((int)var > _solver.vars())
    return VarAssignment::DONT_CARE;
  int phase = _solver.val(var);
  return phase > 0 ? VarAssignment::TRUE : VarAssignment::FALSE;
}

bool CadicalInterfacing::isZeroImplied(unsigned var)
{
  ASS_G(var,0); ASS_L((int)var, _next);
  return _solver.fixed(var);
}

} // namespace SAT
