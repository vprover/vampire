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
#include "Lib/ScopedLet.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "Minisat/core/SolverTypes.h"
#include <limits>

namespace SAT
{

using namespace Shell;  
using namespace Lib;  
  
using namespace Minisat;

const unsigned MinisatInterfacingNewSimp::VAR_MAX = std::numeric_limits<Minisat::Var>::max() / 2;
  
MinisatInterfacingNewSimp::MinisatInterfacingNewSimp(const Shell::Options& opts, bool generateProofs):
  _status(SATISFIABLE)
{
  CALL("MinisatInterfacingNewSimp::MinisatInterfacingNewSimp");
   
  // TODO: consider tuning minisat's options to be set for _solver
  // (or even forwarding them to vampire's options)  
  //_solver.mem_lim(opts.memoryLimit()*2);
  limitMemory(opts.memoryLimit()*1);
}

void MinisatInterfacingNewSimp::reportMinisatOutOfMemory() {
  env.beginOutput();
  reportSpiderStatus('m');
  env.out() << "Minisat ran out of memory" << endl;
  if(env.statistics) {
    env.statistics->print(env.out());
  }
#if VDEBUG
  Debug::Tracer::printStack(env.out());
#endif
  env.endOutput();
  System::terminateImmediately(1);
}

/**
 * Make the solver handle clauses with variables up to @b newVarCnt
 * (but see vampireVar2Minisat!)
 */
void MinisatInterfacingNewSimp::ensureVarCount(unsigned newVarCnt)
{
  CALL("MinisatInterfacingNewSimp::ensureVarCount");
  
  try{
    while(_solver.nVars() < (int)newVarCnt) {
      _solver.newVar();
    }
  } catch (Minisat::OutOfMemoryException&){
    reportMinisatOutOfMemory();
  }
}

unsigned MinisatInterfacingNewSimp::newVar() 
{
  CALL("MinisatInterfacingNewSimp::ensureVarCount");
  
  return minisatVar2Vampire(_solver.newVar());
}

SATSolver::Status MinisatInterfacingNewSimp::solveUnderAssumptions(const SATLiteralStack& assumps, unsigned conflictCountLimit, bool)
{
  CALL("MinisatInterfacingNewSimp::solveUnderAssumptions");

  ASS(!hasAssumptions());

  // load assumptions:
  SATLiteralStack::ConstIterator it(assumps);
  while (it.hasNext()) {
    _assumptions.push(vampireLit2Minisat(it.next()));
  }

  solveModuloAssumptionsAndSetStatus(conflictCountLimit);

  if (_status == SATSolver::UNSATISFIABLE) {
    // unload minisat's internal conflict clause to _failedAssumptionBuffer
    _failedAssumptionBuffer.reset();
    Minisat::LSet& conflict = _solver.conflict;
    for (int i = 0; i < conflict.size(); i++) {
      _failedAssumptionBuffer.push(minisatLit2Vampire(conflict[i]).opposite());
    }
  }

  _assumptions.clear();

  return _status;
}

/**
 * Solve modulo assumptions and set status.
 * @b conflictCountLimit as with addAssumption.
 */
void MinisatInterfacingNewSimp::solveModuloAssumptionsAndSetStatus(unsigned conflictCountLimit) 
{
  CALL("MinisatInterfacingNewSimp::solveModuloAssumptionsAndSetStatus");
  
  // TODO: consider calling simplify(); or only from time to time?
   
  try{
    //int bef = _solver.nVars();
    //cout << "Before: vars " << bef << ", non-unit clauses " << _solver.nClauses() << endl;

    _solver.setConfBudget(conflictCountLimit); // treating UINT_MAX as \infty
    lbool res = _solver.solveLimited(_assumptions,true,true);

    //cout << "After: vars " << bef - _solver.eliminated_vars << ", non-unit clauses " << _solver.nClauses() << endl;
  
    if (res == l_True) {
      _status = SATISFIABLE;
    } else if (res == l_False) {
      _status = UNSATISFIABLE;
    } else {
      _status = UNKNOWN;
    }
  }catch(Minisat::OutOfMemoryException&){
    reportMinisatOutOfMemory();
  }
}

/**
 * Add clause into the solver.
 *
 */
void MinisatInterfacingNewSimp::addClause(SATClause* cl)
{
  CALL("MinisatInterfacingNewSimp::addClause");

  // TODO: consider measuring time
  
  ASS_EQ(_assumptions.size(),0);

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
      reportMinisatOutOfMemory();
  }
}

/**
 * Perform solving and return status.
 */
SATSolver::Status MinisatInterfacingNewSimp::solve(unsigned conflictCountLimit)
{
  CALL("MinisatInterfacingNewSimp::solve");
  
  solveModuloAssumptionsAndSetStatus(conflictCountLimit);
  return _status;
}

void MinisatInterfacingNewSimp::addAssumption(SATLiteral lit) 
{
  CALL("MinisatInterfacingNewSimp::addAssumption");
  
  _assumptions.push(vampireLit2Minisat(lit));
}

SATSolver::VarAssignment MinisatInterfacingNewSimp::getAssignment(unsigned var) 
{
  CALL("MinisatInterfacingNewSimp::getAssignment");
	ASS_EQ(_status, SATISFIABLE);  
	ASS_G(var,0); ASS_LE(var,(unsigned)_solver.nVars());
  lbool res;
    
  Minisat::Var mvar = vampireVar2Minisat(var);  
  if (mvar < _solver.model.size()) {  
    if ((res = _solver.modelValue(mvar)) == l_True) {
      return TRUE;
    } else if (res == l_False) {    
      return FALSE;
    } else {              
      ASSERTION_VIOLATION;
      return NOT_KNOWN;
    }
  } else { // new vars have been added but the model didn't grow yet
    return DONT_CARE;
  }
}

bool MinisatInterfacingNewSimp::isZeroImplied(unsigned var)
{
  CALL("MinisatInterfacingNewSimp::isZeroImplied");
  ASS_G(var,0); ASS_LE(var,(unsigned)_solver.nVars());
  
  /* between calls to _solver.solve*
   value is undefined for all accept zero implied variables */
  return _solver.value(vampireVar2Minisat(var)) != l_Undef;
}

void MinisatInterfacingNewSimp::collectZeroImplied(SATLiteralStack& acc)
{
  CALL("MinisatInterfacingNewSimp::collectZeroImplied");
  
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
  CALL("MinisatInterfacingNewSimp::getZeroImpliedCertificate");
  
  // Currently unused anyway. 
  
  /* The whole SATSolver interface should be revised before
   implementing functions like this one properly */
  
  return 0;
}

} // namespace SAT

