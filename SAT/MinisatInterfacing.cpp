/**
 * @file MinisatInterfacing.cpp
 * Implements class MinisatInterfacing
 */

#include "MinisatInterfacing.hpp"

#include "Lib/ScopedLet.hpp"

namespace SAT
{

using namespace Minisat;
  
MinisatInterfacing::MinisatInterfacing(const Options& opts, bool generateProofs):
  _status(SATISFIABLE)
{
  CALL("MinisatInterfacing::MinisatInterfacing");
  
  // TODO: consider tuning minisat's options to be set for _solver
  // (or even forwarding them to vampire's options)  
}
  
/**
 * Make the solver handle clauses with variables up to @b newVarCnt-1
 */
void MinisatInterfacing::ensureVarCnt(unsigned newVarCnt) 
{
  CALL("MinisatInterfacing::ensureVarCnt");
  
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
  CALL("MinisatInterfacing::solveAndSetStatus");
  
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
 * Add clauses into the solver and saturate.
 *
 * If @c onlyPropagate is true, only unit propagation is done. If
 * unsatisfiability isn't shown in this case, the status is set to UNKNOWN.
 * 
 * Memory-wise, the clauses are owned by the solver from now on.
 */
void MinisatInterfacing::addClauses(SATClauseIterator cit, bool onlyPropagate) 
{
  CALL("MinisatInterfacing::addClauses");
  
  // TODO: consider measuring time
  
  ASS_EQ(_assumptions.size(),0);
  
  while(cit.hasNext()) {
    SATClause* cl=cit.next();
    
    // store to later generate the refutation
    SATClauseList::push(cl,_addedClauses);    
          
    static vec<Lit> mcl;
    mcl.clear();
    
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      SATLiteral l = (*cl)[i];
      ASS_L((int)l.var(),_solver.nVars());
      mcl.push(vampireLit2Minisat(l));
    }
    
    _solver.addClause(mcl);          
  }
  
  solveModuloAssumptionsAndSetStatus(onlyPropagate ? 0 : UINT_MAX);
}

void MinisatInterfacing::addAssumption(SATLiteral lit, unsigned conflictCountLimit) 
{
  CALL("MinisatInterfacing::addAssumption");
  
  _assumptions.push(vampireLit2Minisat(lit));
  
  solveModuloAssumptionsAndSetStatus(conflictCountLimit);
}

SATSolver::VarAssignment MinisatInterfacing::getAssignment(unsigned var) 
{
  CALL("MinisatInterfacing::getAssignment");
	ASS_EQ(_status, SATISFIABLE);  
  ASS_L((int)var,_solver.nVars());
  lbool res;
  if ((res = _solver.modelValue(vampireVar2Minisat(var))) == l_True) {
    return TRUE;
  } else if (res == l_False) {    
    return FALSE;
  } else {    
    ASSERTION_VIOLATION;
    return NOT_KNOWN;
  }
}

void MinisatInterfacing::randomizeAssignment() 
{
  CALL("MinisatInterfacing::randomizeAssignment");
  ASS_EQ(_status, SATISFIABLE);
  
  // temporarily use random polarities for branching heuristics 
  ScopedLet<bool> phaseLet(_solver.rnd_pol,true);
  
  ALWAYS(_solver.solve(_assumptions)); // must again return SATISFIABLE
} 

bool MinisatInterfacing::isZeroImplied(unsigned var)
{
  CALL("MinisatInterfacing::isZeroImplied");
  
  /* between calls to _solver.solve*
   value is undefined for all accept zero implied variables */
  return _solver.value(vampireVar2Minisat(var)) != l_Undef;
}

void MinisatInterfacing::collectZeroImplied(SATLiteralStack& acc)
{
  CALL("MinisatInterfacing::collectZeroImplied");
  
  // TODO: could be made more efficient by inspecting the trail 
  // [new code would be needed in Minisat::solver, though]
  
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

