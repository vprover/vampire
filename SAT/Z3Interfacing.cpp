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
  _varCnt(0), sat2fo(s2f),_status(SATISFIABLE), _solver(_context), _model(_solver.get_first_model()), _showZ3(opts.showZ3())
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
  PrimitiveProofRecordingSATSolver::addClause(cl);

  z3::expr z3clause = _context.bool_val(false);

  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++){
    SATLiteral l = (*cl)[i];
    z3::expr e = getRepresentation(l);
    z3clause = z3clause || e;
  }
  
  if(_showZ3){
    env.beginOutput();
    env.out() << "[Z3] add: " << z3clause << std::endl;
    env.endOutput();
  }
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
  
  // Safe. TODO consider getting zoer-implied
  return false; 
}

void Z3Interfacing::collectZeroImplied(SATLiteralStack& acc)
{
  CALL("Z3Interfacing::collectZeroImplied");
  NOT_IMPLEMENTED;
}

SATClause* Z3Interfacing::getZeroImpliedCertificate(unsigned)
{
  CALL("Z3Interfacing::getZeroImpliedCertificate");
  NOT_IMPLEMENTED;
  
  return 0;
}

//TODO: should handle function/predicate types really
z3::sort Z3Interfacing::getz3sort(unsigned s)
{
  CALL("Z3Interfacing::getz3sort");
  BYPASSING_ALLOCATOR;
  // Deal with known sorts differently
  if(s==Sorts::SRT_BOOL) return _context.bool_sort(); 
  if(s==Sorts::SRT_INTEGER) return _context.int_sort();
  if(s==Sorts::SRT_REAL) return _context.real_sort(); 
  if(s==Sorts::SRT_RATIONAL) return _context.real_sort(); // Drop notion of rationality 

  // Do not currently deal with Array Sorts, they will be treated as user sorts

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

/**
 * Translate a Vampire term into a Z3 term
 * - Assumes term is ground
 * - Translates the ground structure
 * - Some interpretted functions/predicates are handled
 */
z3::expr Z3Interfacing::getz3expr(Term* trm,bool isLit)
{
  CALL("Z3Interfacing::getz3expr");
  BYPASSING_ALLOCATOR;
  ASS(trm);
  ASS(trm->ground());

  //cout << "getz3expr of " << trm->toString() << endl;

    Signature::Symbol* symb; 
    unsigned range_sort;
    BaseType* type;
    bool is_equality = false;
    if(isLit){
      symb = env.signature->getPredicate(trm->functor());
      PredicateType* ptype = symb->predType();
      type = ptype;
      range_sort = Sorts::SRT_BOOL;
      // check for equality
      if(trm->functor()==0){
         is_equality=true;
         ASS(trm->arity()==2);
      }
    }else{
      symb = env.signature->getFunction(trm->functor());
      FunctionType* ftype = symb->fnType(); 
      type = ftype;
      range_sort = ftype->result();
    }

    //if constant treat specially
    if(trm->arity()==0){
      if(symb->integerConstant()){
        IntegerConstantType value = symb->integerValue();
        return _context.int_val(value.toInt());
      }
      if(symb->realConstant()){
        RealConstantType value = symb->realValue();
        return _context.real_val(value.numerator().toInt(),value.denominator().toInt());
      }
      if(symb->rationalConstant()){
        RationalConstantType value = symb->rationalValue();
        return _context.real_val(value.numerator().toInt(),value.denominator().toInt());
      }

      // If not value then create constant symbol
      return _context.constant(symb->name().c_str(),getz3sort(range_sort));
    }
    ASS(trm->arity()>0);

    // Next translate term arguments
    //IMPORTANT - every push_back to args must be matched by a pop_back
    // note that the z3 functions do this already
    z3::expr_vector args = z3::expr_vector(_context);
    for(unsigned i=0;i<trm->arity();i++){
      TermList* arg = trm->nthArgument(i);
      ASS(!arg->isVar());// Term should be ground
      args.push_back(getz3expr(arg->term(),false));
    }

    // dummy return
    z3::expr ret = z3::expr(_context);

   //Check for equality
    if(is_equality){
      ret = args[0] == args[1]; 
      args.pop_back();args.pop_back();
      return ret;
    }

    // Currently just deal with binary interpreted functions
    // - constants dealt with above
    // - unary funs/preds like is_rat interpretation unclear
    if(symb->interpreted() && trm->arity()==2){
      Interpretation interp = static_cast<Signature::InterpretedSymbol*>(symb)->getInterpretation();
      bool skip=false; 

      // Currently all intepretation functions are binary?
      switch(interp){
        // Numerical operations
        case Theory::INT_PLUS:
        case Theory::RAT_PLUS:
        case Theory::REAL_PLUS:
          ret = args[0] + args[1];break;

        case Theory::INT_MINUS:
        case Theory::RAT_MINUS:
        case Theory::REAL_MINUS:
          ret = args[0] - args[1];break;

        case Theory::INT_MULTIPLY:
        case Theory::RAT_MULTIPLY:
        case Theory::REAL_MULTIPLY:
          ret = args[0] * args[1];break;

        case Theory::INT_DIVIDE: //TODO check that they are the same
        case Theory::RAT_DIVIDE:
        case Theory::REAL_DIVIDE:
          ret= args[0] / args[1];break;

       // Numerical comparisons
       case Theory::INT_LESS:
       case Theory::RAT_LESS:
       case Theory::REAL_LESS:
          ret = args[0] < args[1];break;

       case Theory::INT_GREATER:
       case Theory::RAT_GREATER:
       case Theory::REAL_GREATER:
          ret= args[0] > args[1];break;
          
       case Theory::INT_LESS_EQUAL:
       case Theory::RAT_LESS_EQUAL:
       case Theory::REAL_LESS_EQUAL:
          ret= args[0] <= args[1];break;

       case Theory::INT_GREATER_EQUAL:
       case Theory::RAT_GREATER_EQUAL:
       case Theory::REAL_GREATER_EQUAL:
          ret= args[0] >= args[1];break;

        default: skip=true;break; //skip it and treat the function as uninterpretted
      }

      if(!skip){
        args.pop_back();args.pop_back();
        return ret;
      } 

    }
    //TODO check domain_sorts for args in equality and interpretted?
    z3::sort_vector domain_sorts = z3::sort_vector(_context);
    for(unsigned i=0;i<type->arity();i++){
      domain_sorts.push_back(getz3sort(type->arg(i)));
    }
    z3::symbol name = _context.str_symbol(symb->name().c_str());
    z3::func_decl f = _context.function(name,domain_sorts,getz3sort(range_sort));

    // Finally create expr
    z3::expr e = f(args); 
    //cout << "created " << e << endl;
    return e;
}

z3::expr Z3Interfacing::getRepresentation(SATLiteral slit)
{
  CALL("Z3Interfacing::getRepresentation");
  BYPASSING_ALLOCATOR;

  //First, does this represents a ground literal 
  Literal* lit = sat2fo.toFO(slit);
  if(lit && lit->ground()){
    //cout << "getRepresentation of " << lit->toString() << endl;
    // Now translate it into an SMT object 
    try{
      z3::expr e = getz3expr(lit,true);
      //cout << "got rep " << e << endl;
      if(slit.isNegative()) return !e;
      return e;
    }catch(z3::exception& exception){
     cout << "Z3 exception:\n" << exception.msg() << endl;
     ASSERTION_VIOLATION_REP("Failed to create Z3 rep for " + lit->toString());
    }
  }
  //if non ground then just create a propositional variable
  vstring name = "v"+Lib::Int::toString(slit.var());
  z3::expr e = _context.bool_const(name.c_str());
  if(slit.isNegative()) return !e;
  else return e;
}

} // namespace SAT

#endif /** if VZ3 **/
