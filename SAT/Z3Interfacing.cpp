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
#include "Lib/System.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"

#include "Z3Interfacing.hpp"

namespace SAT
{

using namespace Shell;  
using namespace Lib;  

//using namespace z3;
  
Z3Interfacing::Z3Interfacing(const Shell::Options& opts,SAT2FO& s2f, bool unsatCoresForAssumptions):
  _varCnt(0), sat2fo(s2f),_status(SATISFIABLE), _solver(_context),
  _model(_solver.get_first_model()), _assumptions(_context), _unsatCoreForAssumptions(unsatCoresForAssumptions),
  _showZ3(opts.showZ3()),_unsatCoreForRefutations(opts.z3UnsatCores())
{
  CALL("Z3Interfacing::Z3Interfacing");

  if (_unsatCoreForAssumptions) {
    z3::params p(_context);
    p.set(":unsat-core", true);
    _solver.set(p);
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

void Z3Interfacing::addAssumption(SATLiteral lit)
{
  CALL("Z3Interfacing::addAssumption");

  _assumptions.push_back(getRepresentation(lit));
}

SATSolver::Status Z3Interfacing::solve(unsigned conflictCountLimit)
{
  CALL("Z3Interfacing::addClause");
  BYPASSING_ALLOCATOR;

  z3::check_result result = _assumptions.empty() ? _solver.check() : _solver.check(_assumptions);

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

SATSolver::Status Z3Interfacing::solveUnderAssumptions(const SATLiteralStack& assumps, unsigned conflictCountLimit, bool onlyProperSubusets)
{
  CALL("Z3Interfacing::solveUnderAssumptions");

  if (!_unsatCoreForAssumptions) {
    return SATSolverWithAssumptions::solveUnderAssumptions(assumps,conflictCountLimit,onlyProperSubusets);
  }

  ASS(!hasAssumptions());

  _solver.push();

  // load assumptions:
  SATLiteralStack::ConstIterator it(assumps);

  static DHMap<vstring,SATLiteral> lookup;
  lookup.reset();
  unsigned n=0;
  vstring ps="$_$_$";

  while (it.hasNext()) {
    SATLiteral v_assump = it.next();
    z3::expr z_assump = getRepresentation(v_assump);

    vstring p = ps+Int::toString(n++);
    _solver.add(z_assump,p.c_str());
    lookup.insert(p,v_assump);
  }

  z3::check_result result = _solver.check();

  _solver.pop();

  if (result == z3::check_result::unsat) {

    _failedAssumptionBuffer.reset();

    z3::expr_vector  core = _solver.unsat_core();
    for (unsigned i = 0; i < core.size(); i++) {
      z3::expr ci = core[i];
      vstring cip = Z3_ast_to_string(_context,ci);
      SATLiteral v_assump = lookup.get(cip);
      _failedAssumptionBuffer.push(v_assump);
    }

    return UNSATISFIABLE;
  } else if (result == z3::check_result::sat) {
    _model = _solver.get_model();
    return SATISFIABLE;
  } else {
    return UNKNOWN;
  }
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

bool Z3Interfacing::isZeroImplied(unsigned var)
{
  CALL("Z3Interfacing::isZeroImplied");
  
  // Safe. TODO consider getting zero-implied
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

  // Deal with arrays
  if(env.sorts->hasStructuredSort(s,Sorts::StructuredSort::ARRAY)){
    
    z3::sort index_sort = getz3sort(env.sorts->getArraySort(s)->getIndexSort());
    z3::sort value_sort = getz3sort(env.sorts->getArraySort(s)->getInnerSort());
 
    return _context.array_sort(index_sort,value_sort);
  } 

  // Use new interface for uninterpreted sorts, I think this is not less efficient
  return _context.uninterpreted_sort(Lib::Int::toString(s).c_str());
/*
  // If sort exists, return it
  if(_sorts.find(s)){
    return z3::sort(_context,_sorts.get(s));
  }
  // Else create a new one, I think this is how! Mix of C and C++ API calls!
  Z3_symbol sname = Z3_mk_string_symbol(_context.get(),Lib::Int::toString(s).c_str());
  Z3_sort sort = Z3_mk_uninterpreted_sort(_context.get(),sname);
  _sorts.insert(s,sort);
  return z3::sort(_context,sort); 
*/
}

/**
 * Translate a Vampire term into a Z3 term
 * - Assumes term is ground
 * - Translates the ground structure
 * - Some interpreted functions/predicates are handled
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
      if(env.signature->isFoolConstantSymbol(true,trm->functor())){
        return _context.bool_val(true);
      }
      if(env.signature->isFoolConstantSymbol(false,trm->functor())){
        return _context.bool_val(false);
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

    // Currently do not deal with all intepreted operations, should extend 
    // - constants dealt with above
    // - unary funs/preds like is_rat interpretation unclear
    if(symb->interpreted()){
      Interpretation interp = static_cast<Signature::InterpretedSymbol*>(symb)->getInterpretation();
      bool skip=false; 
      unsigned argsToPop=theory->getArity(interp);

      if(theory->isStructuredSortInterpretation(interp)){

        switch(theory->convertToStructured(interp)){
          case Theory::StructuredSortInterpretation::ARRAY_SELECT:
          case Theory::StructuredSortInterpretation::ARRAY_BOOL_SELECT:
            // select(array,index)
            ret = select(args[0],args[1]);
            break;

          case Theory::StructuredSortInterpretation::ARRAY_STORE:
            // store(array,index,value)
            ret = store(args[0],args[1],args[2]);
            break;

          default:
            skip=true;//skip it and treat the function as uninterpretted
            break;
        }

      }else{

      switch(interp){
        // Numerical operations

        case Theory::INT_UNARY_MINUS:
        case Theory::RAT_UNARY_MINUS:
        case Theory::REAL_UNARY_MINUS:
          ret = -args[0];
          break;

        case Theory::INT_PLUS:
        case Theory::RAT_PLUS:
        case Theory::REAL_PLUS:
          ret = args[0] + args[1];
          break;

        case Theory::INT_MINUS:
        case Theory::RAT_MINUS:
        case Theory::REAL_MINUS:
          ret = args[0] - args[1];
          break;

        case Theory::INT_MULTIPLY:
        case Theory::RAT_MULTIPLY:
        case Theory::REAL_MULTIPLY:
          ret = args[0] * args[1];
          break;

        // Not sure of rounding in these cases
        //case Theory::INT_DIVIDE: //TODO check that they are the same
        //case Theory::RAT_DIVIDE:
        //case Theory::REAL_DIVIDE:
        //  ret= args[0] / args[1];
        //  break;

        // No int quotient
        case Theory::RAT_QUOTIENT:
        case Theory::REAL_QUOTIENT:
        case Theory::INT_QUOTIENT_E: // this is how their header translates _e
        case Theory::RAT_QUOTIENT_E: // I assume the built-in division does this
        case Theory::REAL_QUOTIENT_E: // euclidian rounding as default
          ret= args[0] / args[1];
          break;

        case Theory::RAT_TO_INT:
        case Theory::REAL_TO_INT:
        case Theory::INT_FLOOR:
        case Theory::RAT_FLOOR:
        case Theory::REAL_FLOOR:
          ret = to_real(to_int(args[0])); 
          break;

        case Theory::INT_TO_REAL:
        case Theory::RAT_TO_REAL:
        case Theory::INT_TO_RAT: //I think this works also
          ret = to_real(args[0]);
          break;

        case Theory::INT_CEILING:
        case Theory::RAT_CEILING:
        case Theory::REAL_CEILING:
          ret = ceiling(args[0]);
          break;

        case Theory::INT_TRUNCATE:
        case Theory::RAT_TRUNCATE:
        case Theory::REAL_TRUNCATE:
          ret = truncate(args[0]); 
          break;

        case Theory::INT_ROUND:
        case Theory::RAT_ROUND:
        case Theory::REAL_ROUND:
          {
            z3::expr t = args[0];
            z3::expr i = to_int(t);
            z3::expr i2 = i + _context.real_val(1,2);
            ret = ite(t > i2, i+1, ite(t==i2, ite(is_even(i),i,i+1),i));
            break;
          }

         case Theory::INT_QUOTIENT_T:
         case Theory::RAT_QUOTIENT_T:
         case Theory::REAL_QUOTIENT_T:
           ret = truncate(args[0] / args[1]);
           break;

         case Theory::INT_QUOTIENT_F:
         case Theory::RAT_QUOTIENT_F:
         case Theory::REAL_QUOTIENT_F:
           ret = to_real(to_int(args[0] / args[1]));
           break;

         // remainder_t and remainder_r not handled

         case Theory::INT_REMAINDER_E:
         case Theory::RAT_REMAINDER_E:
         case Theory::REAL_REMAINDER_E:
           ret = z3::expr(_context, Z3_mk_mod(_context, args[0], args[1]));
           break;

       // Numerical comparisons
       // is_rat and to_rat not supported

       case Theory::INT_IS_INT:
       case Theory::RAT_IS_INT:
       case Theory::REAL_IS_INT:
         ret = z3::expr(_context,Z3_mk_is_int(_context,args[0]));
         break;

       case Theory::INT_LESS:
       case Theory::RAT_LESS:
       case Theory::REAL_LESS:
          ret = args[0] < args[1];
          break;

       case Theory::INT_GREATER:
       case Theory::RAT_GREATER:
       case Theory::REAL_GREATER:
          ret= args[0] > args[1];
          break;
          
       case Theory::INT_LESS_EQUAL:
       case Theory::RAT_LESS_EQUAL:
       case Theory::REAL_LESS_EQUAL:
          ret= args[0] <= args[1];
          break;

       case Theory::INT_GREATER_EQUAL:
       case Theory::RAT_GREATER_EQUAL:
       case Theory::REAL_GREATER_EQUAL:
          ret= args[0] >= args[1];
          break;

        default: 
          skip=true;//skip it and treat the function as uninterpretted
          break;
      }
      }

      if(!skip){
        while(argsToPop--){ args.pop_back(); }
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

  //First, does this represent a ground literal
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
     reportSpiderFail();
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

SATClause* Z3Interfacing::getRefutation() {

    if(!_unsatCoreForRefutations)
      return PrimitiveProofRecordingSATSolver::getRefutation(); 


    z3::solver solver(_context);
    z3::params p(_context);
    p.set(":unsat-core", true);
    solver.set(p);

    SATClauseList* added = PrimitiveProofRecordingSATSolver::getRefutationPremiseList();
    SATClauseList::Iterator cit(added);
    unsigned n=0;
    vstring ps="$_$_$";

    DHMap<vstring,SATClause*> lookup;

    while(cit.hasNext()){
      SATClause* cl = cit.next();
      z3::expr z3clause = _context.bool_val(false);
      unsigned clen=cl->length();
      for(unsigned i=0;i<clen;i++){
        SATLiteral l = (*cl)[i];
        z3::expr e = getRepresentation(l);
        z3clause = z3clause || e;
      }
      vstring p = ps+Int::toString(n++);
      //cout << p << ": " << cl->toString() << endl;
      solver.add(z3clause,p.c_str());
      lookup.insert(p,cl);
    }
    //TODO add assertion
    //cout << solver.check() << endl;
    solver.check();

    SATClauseList* prems = 0;

    z3::expr_vector  core = solver.unsat_core();
    for (unsigned i = 0; i < core.size(); i++) {
        z3::expr ci = core[i];
        vstring cip = Z3_ast_to_string(_context,ci);
        SATClause* cl = lookup.get(cip);
        SATClauseList::push(cl,prems);
        //std::cout << cl->toString() << "\n";
    }

    SATClause* refutation = new(0) SATClause(0);
    refutation->setInference(new PropInference(prems));

    return refutation; 
}


} // namespace SAT

#endif /** if VZ3 **/
