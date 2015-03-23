/**
 * @file Z3Interfacing.cpp
 * Implements class Z3Interfacing
 */

#include "Z3Interfacing.hpp"
#include<z3++.h>

namespace SAT
{

using namespace Shell;  
using namespace Lib;  
  
using namespace z3;
  
Z3Interfacing::Z3Interfacing(const Shell::Options& opts, bool generateProofs):
  _status(SATISFIABLE)
{
  CALL("Z3Interfacing::Z3Interfacing");
  
  _solver(_context); 

  // Here is where we would set context parameters i.e.
  //params p(c);
  //p.set("unsat_core",true);
  //_solver.set(p);
}
  
/**
 * Add clauses into the solver and saturate.
 *
 * If @c onlyPropagate is true, only unit propagation is done. If
 * unsatisfiability isn't shown in this case, the status is set to UNKNOWN.
 * 
 * Memory-wise, the clauses are owned by the solver from now on.
 * 
 * @useInPartialModel is ignored as this solver generates a total model
 */
void Z3Interfacing::addClauses(SATClauseIterator cit, 
        bool onlyPropagate, bool useInPartialModel)
{
  CALL("Z3Interfacing::addClauses");
  
  ASS_EQ(_assumptions.size(),0);

  while(cit.hasNext()){
    addClause(cit.next());
  }

}

void Z3Interfacing::addClause

void Z3Interfacing::addAssumption(SATLiteral lit, unsigned conflictCountLimit) 
{
  CALL("Z3Interfacing::addAssumption");
  
}

SATSolver::VarAssignment Z3Interfacing::getAssignment(unsigned var) 
{
  CALL("Z3Interfacing::getAssignment");
  return NOT_KNOWN;
}

void Z3Interfacing::randomizeAssignment() 
{
  CALL("Z3Interfacing::randomizeAssignment");
} 

bool Z3Interfacing::isZeroImplied(unsigned var)
{
  CALL("Z3Interfacing::isZeroImplied");
  
  return false; 
}

void Z3Interfacing::collectZeroImplied(SATLiteralStack& acc)
{
  CALL("Z3Interfacing::collectZeroImplied");
  
}

SATClause* Z3Interfacing::getZeroImpliedCertificate(unsigned)
{
  CALL("Z3Interfacing::getZeroImpliedCertificate");
  
  return 0;
}

SATClause* Z3Interfacing::getRefutation() 
{
  CALL("Z3Interfacing::getRefutation");
  
	return 0; 
}

} // namespace SAT

