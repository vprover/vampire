/**
 * @file Z3Interfacing.cpp
 * Implements class Z3Interfacing
 */

#if VZ3

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"
#include "SATInference.hpp"

#include "Z3Interfacing.hpp"

namespace SAT
{

using namespace Shell;  
using namespace Lib;  

//using namespace z3;
  
Z3Interfacing::Z3Interfacing(const Shell::Options& opts, bool generateProofs):
  _status(SATISFIABLE), _solver(_context), _model(_solver.get_first_model()), _addedClauses(0)
{
  CALL("Z3Interfacing::Z3Interfacing");
  

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
void Z3Interfacing::addClauses(SATClauseIterator cit) 
{
  CALL("Z3Interfacing::addClauses");
  
  while(cit.hasNext()){
    addClause(cit.next());
  }

}

void Z3Interfacing::addClause(SATClause* cl)
{
  CALL("Z3Interfacing::addClause");
  BYPASSING_ALLOCATOR;
  ASS(cl);

  // store to later generate the refutation
  SATClauseList::push(cl,_addedClauses);

  z3::expr z3clause = _context.bool_val(false);

  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++){
    SATLiteral l = (*cl)[i];
    z3::expr e = getRepresentation(l.var());
    if(l.isNegative()) e = !e;
    z3clause = z3clause || e;
  }
  
  cout << "add " << z3clause << endl;
  _solver.add(z3clause);

}

SATSolver::Status Z3Interfacing::solve(unsigned conflictCountLimit)
{
  CALL("Z3Interfacing::addClause");
  BYPASSING_ALLOCATOR;

  z3::check_result result = _solver.check();

  cout << "solve result: " << result << endl;

  switch(result){
    case z3::check_result::unsat:
      _status = UNSATISFIABLE; 
      break;
    case z3::check_result::sat:
      _status = SATISFIABLE;
      _model = _solver.get_model();
      cout << "model : " << endl;
      for(unsigned i=0; i < _model.size(); i++){
        z3::func_decl v = _model[i];
        cout << v.name() << " = " << _model.get_const_interp(v) << endl;
      }
      break;
    case z3::check_result::unknown:
      _status = UNKNOWN;
      break;
#if VDEBUG
    default: ASSERTION_VIOLATION;
#endif
  }
  return _status;
}

void Z3Interfacing::addAssumption(SATLiteral lit, unsigned conflictCountLimit) 
{
  CALL("Z3Interfacing::addAssumption");
  
}

SATSolver::VarAssignment Z3Interfacing::getAssignment(unsigned var) 
{
  CALL("Z3Interfacing::getAssignment");
  BYPASSING_ALLOCATOR;

  ASS_EQ(_status,SATISFIABLE);

  z3::expr rep = getRepresentation(var);
  cout << "rep is " << rep << endl;
  z3::expr assignment = _model.eval(rep);
  cout << "ass is " << assignment << endl;

  static z3::expr t = _context.bool_val(true);
  static z3::expr f = _context.bool_val(false);

  cout << t << " and " << f << endl;

  if(assignment == t){ 
  cout << "returning true for " << var << endl;
    return TRUE;
  }
  if(assignment == f){ 
  cout << "returning false for " << var << endl;
    return FALSE;
  }

  cout << "returning don't care for " << var << endl;
  return DONT_CARE;
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
  
        ASS_EQ(_status,UNSATISFIABLE);
 
  // connect the added clauses ... 
  SATClauseList* prems = _addedClauses;
 
  // ... with the current assumptions
/*
  for (int i=0; i < _assumptions.size(); i++) {
    SATClause* unit = new(1) SATClause(1);
    (*unit)[0] = minisatLit2Vampire(_assumptions[i]);
    unit->setInference(new AssumptionInference());
    SATClauseList::push(unit,prems);
  }
*/

    SATClause* refutation = new(0) SATClause(0);
    refutation->setInference(new PropInference(prems));

    cout << "returing refutation " << refutation << endl;

    return refutation;

}

z3::expr Z3Interfacing::getRepresentation(unsigned var)
{
  CALL("Z3Interfacing::getRepresentation");
  BYPASSING_ALLOCATOR;

  vstring name = "v"+Lib::Int::toString(var);
  z3::expr e = _context.bool_const(name.c_str());
  return e;
}

} // namespace SAT

#endif /** if VZ3 **/
