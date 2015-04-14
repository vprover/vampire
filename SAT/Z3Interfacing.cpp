/**
 * @file Z3Interfacing.cpp
 * Implements class Z3Interfacing
 */

#if VZ3

#include "Forwards.hpp"

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"
#include "SATInference.hpp"

#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"

#include "Z3Interfacing.hpp"

namespace SAT
{

using namespace Shell;  
using namespace Lib;  

//using namespace z3;
  
Z3Interfacing::Z3Interfacing(const Shell::Options& opts,SAT2FO& s2f, bool generateProofs):
  sat2fo(s2f),_status(SATISFIABLE), _solver(_context), _model(_solver.get_first_model()), _addedClauses(0)
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
    z3::expr e = getRepresentation(l);
    z3clause = z3clause || e;
  }
  
  //cout << "add " << z3clause << endl;
  _solver.add(z3clause);

}

SATSolver::Status Z3Interfacing::solve(unsigned conflictCountLimit)
{
  CALL("Z3Interfacing::addClause");
  BYPASSING_ALLOCATOR;

  z3::check_result result = _solver.check();

  //cout << "solve result: " << result << endl;

  switch(result){
    case z3::check_result::unsat:
      _status = UNSATISFIABLE; 
      break;
    case z3::check_result::sat:
      _status = SATISFIABLE;
      _model = _solver.get_model();
      //cout << "model : " << endl;
      //for(unsigned i=0; i < _model.size(); i++){
      //  z3::func_decl v = _model[i];
      //  cout << v.name() << " = " << _model.get_const_interp(v) << endl;
      //}
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

  z3::expr rep = getRepresentation(SATLiteral(var,1));
  z3::expr assignment = _model.eval(rep);
  //cout << "ass is " << assignment << endl;


  if(Z3_get_bool_value(_context,assignment)==Z3_L_TRUE){
  //cout << "returning true for " << var << endl;
    return TRUE;
  }
  if(Z3_get_bool_value(_context,assignment)==Z3_L_FALSE){
  //cout << "returning false for " << var << endl;
    return FALSE;
  }

  //cout << "returning don't care for " << var << endl;
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

    //cout << "returing refutation " << refutation << endl;

    return refutation;

}

z3::sort Z3Interfacing::getz3sort(unsigned s)
{
  CALL("Z3Interfacing::getz3sort");
  BYPASSING_ALLOCATOR;
  // Deal with known sorts differently
  if(s==Sorts::SRT_BOOL) return _context.bool_sort(); 
  if(s==Sorts::SRT_INTEGER) return _context.int_sort();
  if(s==Sorts::SRT_REAL) return _context.real_sort(); 

  // Not sure what to do with rationals yet 
  //if(s==SRT_RATIONAL) return sort(_context,Z3__SORT);

  // Cannot currently deal with Array Sorts, they will be treated as user sorts

  // If sort exists, return it
  if(_sorts.find(s)){
    return z3::sort(_context,_sorts.get(s));
  }
  // Else create a new one, I think this is how! Mix of C and C++ API calls!
  Z3_symbol sname = Z3_mk_string_symbol(_context.get(),Lib::Int::toString(s).c_str());
  Z3_sort sort = Z3_mk_uninterpreted_sort(_context.get(),sname);
  _sorts.insert(s,sort);
  return z3::sort(_context,sort); 

}

z3::expr Z3Interfacing::getz3expr(Term* trm,bool isLit)
{
  CALL("Z3Interfacing::getz3expr");
  BYPASSING_ALLOCATOR;

    Signature::Symbol* symb; 
    unsigned range_sort;
    BaseType* type;
    if(isLit){
      symb = env.signature->getPredicate(trm->functor());
      PredicateType* ptype = symb->predType();
      type = ptype;
      range_sort = Sorts::SRT_BOOL;
    }else{
      symb = env.signature->getFunction(trm->functor());
      FunctionType* ftype = symb->fnType(); 
      type = ftype;
      range_sort = ftype->result();
    }
    z3::sort_vector domain_sorts = z3::sort_vector(_context); 
    for(unsigned i=0;i<type->arity();i++){
      domain_sorts.push_back(getz3sort(type->arg(i)));
    }
    z3::symbol name = _context.str_symbol(symb->name().c_str());
    z3::func_decl f = _context.function(name,domain_sorts,getz3sort(range_sort)); 

    // Next translate term arguments
    z3::expr_vector args = z3::expr_vector(_context);
    for(unsigned i=0;i<trm->arity();i++){
      TermList* arg = trm->nthArgument(i);
      ASS(!arg->isVar());// Term should be ground
      args.push_back(getz3expr(arg->term(),false));
    }

    if(symb->isInterpreted()){


    }

    // Finally create expr
    z3::expr e = f(args); 
    return e;
}

z3::expr Z3Interfacing::getRepresentation(SATLiteral slit)
{
  CALL("Z3Interfacing::getRepresentation");
  BYPASSING_ALLOCATOR;

  //First, is does this represents a ground literal 
  Literal* lit = sat2fo.toFO(slit);
  if(lit && lit->ground()){
    // Now translate it into an SMT object 
    z3::expr e = getz3expr(lit,true);
    if(slit.isNegative()) return !e;
    return e;
  }
  //if non ground then just create a propositional variable
  vstring name = "v"+Lib::Int::toString(slit.var());
  z3::expr e = _context.bool_const(name.c_str());
  if(slit.isNegative()) return !e;
  else return e;
}

} // namespace SAT

#endif /** if VZ3 **/
