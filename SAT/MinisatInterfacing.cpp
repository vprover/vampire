/**
 * @file MinisatInterfacing.cpp
 * Implements class MinisatInterfacing
 */

#include "MinisatInterfacing.hpp"

#include "Lib/ScopedLet.hpp"

namespace SAT
{

using namespace Shell;  
using namespace Lib;  
  
using namespace Minisat;
  
MinisatInterfacing::MinisatInterfacing(const Shell::Options& opts, bool generateProofs):
  _status(SATISFIABLE), _addedClauses(0)
{
  CALL("MinisatInterfacing::MinisatInterfacing");
  
  // TODO: consider tuning minisat's options to be set for _solver
  // (or even forwarding them to vampire's options)  
}
  
/**
 * Make the solver handle clauses with variables up to @b newVarCnt
 * (but see vampireVar2Minisat!)
 */
void MinisatInterfacing::ensureVarCount(unsigned newVarCnt)
{
  CALL("MinisatInterfacing::ensureVarCount");
  
  while(_solver.nVars() < (int)newVarCnt) {
    _solver.newVar();
  }
}

/**
 * Solve modulo assumptions and set status.
 * @b conflictCountLimit as with addAssumption.
 */
void MinisatInterfacing::solveModuloAssumptionsAndSetStatus(unsigned conflictCountLimit) 
{
  CALL("MinisatInterfacing::solveModuloAssumptionsAndSetStatus");
  
  // TODO: consider calling simplify(); or only from time to time?
    
  _solver.setConfBudget(conflictCountLimit); // treating UINT_MAX as \infty     
  lbool res = _solver.solveLimited(_assumptions);
  
  if (res == l_True) {
    _status = SATISFIABLE;
  } else if (res == l_False) {
    _status = UNSATISFIABLE;    
  } else {
    _status = UNKNOWN;
  }
}

/**
 * Add clause into the solver.
 *
 */
void MinisatInterfacing::addClause(SATClause* cl)
{
  CALL("MinisatInterfacing::addClause");
  
  // TODO: consider measuring time
  
  ASS_EQ(_assumptions.size(),0);
    
  // store to later generate the refutation
  SATClauseList::push(cl,_addedClauses);
          
  static vec<Lit> mcl;
  mcl.clear();
    
  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++) {
    SATLiteral l = (*cl)[i];
    mcl.push(vampireLit2Minisat(l));
  }

  _solver.addClause(mcl);
}

/**
 * Perform solving and return status.
 */
SATSolver::Status MinisatInterfacing::solve(unsigned conflictCountLimit)
{
  CALL("MinisatInterfacing::solve");
  
  solveModuloAssumptionsAndSetStatus(conflictCountLimit);
  return _status;
}

void MinisatInterfacing::addAssumption(SATLiteral lit) 
{
  CALL("MinisatInterfacing::addAssumption");
  
  _assumptions.push(vampireLit2Minisat(lit));
}

SATSolver::VarAssignment MinisatInterfacing::getAssignment(unsigned var) 
{
  CALL("MinisatInterfacing::getAssignment");
	ASS_EQ(_status, SATISFIABLE);  
	ASS_G(var,0); ASS_LE(var,_solver.nVars());
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

bool MinisatInterfacing::isZeroImplied(unsigned var)
{
  CALL("MinisatInterfacing::isZeroImplied");
  ASS_G(var,0); ASS_LE(var,_solver.nVars());
  
  /* between calls to _solver.solve*
   value is undefined for all accept zero implied variables */
  return _solver.value(vampireVar2Minisat(var)) != l_Undef;
}

void MinisatInterfacing::collectZeroImplied(SATLiteralStack& acc)
{
  CALL("MinisatInterfacing::collectZeroImplied");
  
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

SATClause* MinisatInterfacing::getZeroImpliedCertificate(unsigned)
{
  CALL("MinisatInterfacing::getZeroImpliedCertificate");
  
  // Currently unused anyway. 
  
  /* The whole SATSolver interface should be revised before
   implementing functions like this one properly */
  
  return 0;
}

SATClause* MinisatInterfacing::getRefutation() 
{
  CALL("MinisatInterfacing::getRefutation");
  
	ASS_EQ(_status,UNSATISFIABLE);
  
  // connect the added clauses ... 
  SATClauseList* prems = _addedClauses;
  
  // ... with the current assumptions
  for (int i=0; i < _assumptions.size(); i++) {
    SATClause* unit = new(1) SATClause(1);
    (*unit)[0] = minisatLit2Vampire(_assumptions[i]);
    unit->setInference(new AssumptionInference());
    SATClauseList::push(unit,prems);
  }
  	        
	SATClause* refutation = new(0) SATClause(0);
	refutation->setInference(new PropInference(prems));

	return refutation; 
}

} // namespace SAT

