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

SATSolver::Status CadicalInterfacing::solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit)
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
SATSolver::Status CadicalInterfacing::solveLimited(unsigned conflictCountLimit)
{
  _assumptions.clear();
  solveModuloAssumptionsAndSetStatus(conflictCountLimit);
  return _status;
}

SATSolver::VarAssignment CadicalInterfacing::getAssignment(unsigned var)
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

SATClauseList* CadicalInterfacing::minimizePremiseList(SATClauseList* premises, SATLiteralStack& assumps)
{
  CaDiCaL::Solver solver;

  // TODO this should be a vector
  static DHMap<int,SATClause*> var2prem;
  var2prem.reset();

  static std::vector<int> ass; // assumptions for the final call
  ass.clear();

  int cl_no = 0;

  SATClauseList* it= premises;
  while(it) {
    // store the link for fast lookup
    var2prem.insert(cl_no,it->head());

    // corresponding assumption
    ass.push_back(cl_no + 1); // posive as the assumption

    // allocate the var for the clause
    solver.reserve(cl_no + 1);

    cl_no++;
    it=it->tail();
  }

  // from now on, offset will mark the translation of premises' original variables to the ones in solver here
  int offset = cl_no;

  // start counting from 0 and traversing from the beginning again
  cl_no = 0;
  it = premises;
  while(it) {
    SATClause* cl = it->head();

    // translate the clause to minisat's language (shift vars by offset)
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      SATLiteral l = (*cl)[i];
      int var = offset + l.var();

      // make sure vars are allocated
      solver.reserve(var);
      solver.add(vampire2Cadical(l.positive(), var));
    }

    solver.add(-(cl_no + 1));
    solver.add(0);

    cl_no++;
    it=it->tail();
  }

  // add assumptions from assumps
  SATLiteralStack::Iterator ait(assumps);
  while (ait.hasNext()) {
    SATLiteral l = ait.next();
    int var = offset + l.var();

    ass.push_back(vampire2Cadical(l.positive(), var));
  }

  // solve
  for(int assumption : ass)
    solver.assume(assumption);
  ALWAYS(solver.solve() == CaDiCaL::UNSATISFIABLE); // should be unsat

  SATClauseList* result = SATClauseList::empty();

  // extract the used ones
  for (int assumption : ass) {
    if(!solver.failed(assumption))
      continue;

    SATClause* cl;

    if (var2prem.find(assumption - 1,cl)) {
      SATClauseList::push(cl,result);
    } // it could also be one of the "assumps"
  }
  return result;
}

} // namespace SAT
