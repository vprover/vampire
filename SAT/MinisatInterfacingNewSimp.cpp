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
 * @file MinisatInterfacingNewSimp.cpp
 * Implements class MinisatInterfacingNewSimp
 */

#include "Forwards.hpp"

#include "MinisatInterfacingNewSimp.hpp"

#include "Lib/System.hpp"
#include "Shell/UIHelper.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Debug/Tracer.hpp"

#include "Minisat/core/SolverTypes.h"
#include <limits>

namespace SAT
{

using namespace std;
using namespace Shell;  
using namespace Lib;  
  
using namespace Minisat;

const unsigned MinisatInterfacingNewSimp::VAR_MAX = std::numeric_limits<Minisat::Var>::max() / 2;

/**
 * Make the solver handle clauses with variables up to @b newVarCnt
 * (but see vampireVar2Minisat!)
 */
void MinisatInterfacingNewSimp::ensureVarCount(unsigned newVarCnt)
{
  try{
    while(_solver.nVars() < (int)newVarCnt) {
      _solver.newVar();
    }
  } catch (Minisat::OutOfMemoryException&){
    throw std::bad_alloc();
  }
}

unsigned MinisatInterfacingNewSimp::newVar() 
{
  return minisatVar2Vampire(_solver.newVar());
}

SATSolver::Status MinisatInterfacingNewSimp::solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit)
{
  // load assumptions:
  SATLiteralStack::ConstIterator it(assumps);
  _assumptions.clear();
  while (it.hasNext()) {
    _assumptions.push(vampireLit2Minisat(it.next()));
  }

  solveModuloAssumptionsAndSetStatus(conflictCountLimit);
  return _status;
}

/**
 * Solve modulo assumptions and set status.
 * @b conflictCountLimit as with addAssumption.
 */
void MinisatInterfacingNewSimp::solveModuloAssumptionsAndSetStatus(unsigned conflictCountLimit) 
{
  // TODO: consider calling simplify(); or only from time to time?
   
  try{
    //int bef = _solver.nVars();
    //cout << "Before: vars " << bef << ", non-unit clauses " << _solver.nClauses() << endl;

    _solver.setConfBudget(conflictCountLimit); // treating UINT_MAX as \infty
    lbool res = _solver.solveLimited(_assumptions,true,true);

    //cout << "After: vars " << bef - _solver.eliminated_vars << ", non-unit clauses " << _solver.nClauses() << endl;
  
    if (res == l_True) {
      _status = Status::SATISFIABLE;
    } else if (res == l_False) {
      _status = Status::UNSATISFIABLE;
    } else {
      _status = Status::UNKNOWN;
    }
  }catch(Minisat::OutOfMemoryException&){
    throw std::bad_alloc();
  }
}

SATLiteralStack MinisatInterfacingNewSimp::failedAssumptions() {
  ASS_EQ(_status, Status::UNSATISFIABLE)

  SATLiteralStack result;
  for (int i = 0; i < _solver.conflict.size(); i++)
    result.push(minisatLit2Vampire(_solver.conflict[i]).opposite());
  return result;
}

/**
 * Add clause into the solver.
 *
 */
void MinisatInterfacingNewSimp::addClause(SATClause* cl)
{
  // TODO: consider measuring time
  try {
    static vec<Lit> mcl;
    mcl.clear();

    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      SATLiteral l = (*cl)[i];
      mcl.push(vampireLit2Minisat(l));
    }
    _solver.addClause(mcl);
  } catch (Minisat::OutOfMemoryException&){
    throw std::bad_alloc();
  }
}

/**
 * Perform solving and return status.
 */
SATSolver::Status MinisatInterfacingNewSimp::solveLimited(unsigned conflictCountLimit)
{
  _assumptions.clear();
  solveModuloAssumptionsAndSetStatus(conflictCountLimit);
  return _status;
}

SATSolver::VarAssignment MinisatInterfacingNewSimp::getAssignment(unsigned var) 
{
	ASS_EQ(_status, Status::SATISFIABLE);
	ASS_G(var,0); ASS_LE(var,(unsigned)_solver.nVars());
  lbool res;

  Minisat::Var mvar = vampireVar2Minisat(var);
  if (mvar < _solver.model.size()) {
    if ((res = _solver.modelValue(mvar)) == l_True) {
      return VarAssignment::TRUE;
    } else if (res == l_False) {
      return VarAssignment::FALSE;
    } else {
      ASSERTION_VIOLATION;
      return VarAssignment::NOT_KNOWN;
    }
  } else { // new vars have been added but the model didn't grow yet
    return VarAssignment::DONT_CARE;
  }
}

bool MinisatInterfacingNewSimp::isZeroImplied(unsigned var)
{
  ASS_G(var,0); ASS_LE(var,(unsigned)_solver.nVars());
  
  /* between calls to _solver.solve*
   value is undefined for all accept zero implied variables */
  return _solver.value(vampireVar2Minisat(var)) != l_Undef;
}

void MinisatInterfacingNewSimp::collectZeroImplied(SATLiteralStack& acc)
{
  // TODO: could be made more efficient by inspecting the trail 
  // [new code would be needed in Minisat::solver, though]
  
  // Minisat's variables start from 0
  for (Minisat::Var v = 0; v < _solver.nVars(); v++) {
    lbool val = _solver.value(v);
    if (val != l_Undef) { // see isZeroImplied
      
      // the lit needs to be negated, if the variable alone is false
      acc.push(minisatLit2Vampire(mkLit(v,val == l_False)));
    }
  }        
}

SATClause* MinisatInterfacingNewSimp::getZeroImpliedCertificate(unsigned)
{
  // Currently unused anyway. 
  
  /* The whole SATSolver interface should be revised before
   implementing functions like this one properly */
  
  return 0;
}

} // namespace SAT

