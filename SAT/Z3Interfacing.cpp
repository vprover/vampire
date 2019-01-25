
/*
 * File Z3Interfacing.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Z3Interfacing.cpp
 * Implements class Z3Interfacing
 */

#if VZ3

#define DPRINT 0

#include "Forwards.hpp"

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"
#include "SATInference.hpp"

#include "Lib/Environment.hpp"
#include "Lib/System.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/SortHelper.hpp"

#include "Shell/UIHelper.hpp"

#include "Indexing/TermSharing.hpp"

#include "Z3Interfacing.hpp"

namespace SAT
{

using namespace Shell;
using namespace Lib;

//using namespace z3;

Z3Interfacing::Z3Interfacing(const Shell::Options& opts,SAT2FO& s2f, bool unsatCoresForAssumptions):
  _varCnt(0), sat2fo(s2f),_status(SATISFIABLE), _solver(_context),
  _model((_solver.check(),_solver.get_model())), _assumptions(_context), _unsatCoreForAssumptions(unsatCoresForAssumptions),
  _showZ3(opts.showZ3()),_unsatCoreForRefutations(opts.z3UnsatCores())
{
  CALL("Z3Interfacing::Z3Interfacing");
  _solver.reset();

    z3::params p(_context);
  if (_unsatCoreForAssumptions) {
    p.set(":unsat-core", true);
  }
    //p.set(":smtlib2-compliant",true);
    _solver.set(p);
}

unsigned Z3Interfacing::newVar()
{
  CALL("Z3Interfacing::newVar");

  ++_varCnt;

  // to make sure all the literals we will ask about later have allocated counterparts internally
  getRepresentation(SATLiteral(_varCnt,1),false);

  return _varCnt;
}

void Z3Interfacing::addClause(SATClause* cl,bool withGuard)
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
    z3::expr e = getRepresentation(l,withGuard);
    z3clause = z3clause || e;
  }

  if(_showZ3){
    env.beginOutput();
    env.out() << "[Z3] add (clause): " << z3clause << std::endl;
    env.endOutput();
  }
  _solver.add(z3clause);
}

void Z3Interfacing::addAssumption(SATLiteral lit,bool withGuard)
{
  CALL("Z3Interfacing::addAssumption");

  _assumptions.push_back(getRepresentation(lit,withGuard));
}

SATSolver::Status Z3Interfacing::solve(unsigned conflictCountLimit)
{
  CALL("Z3Interfacing::solve");
  BYPASSING_ALLOCATOR;

  z3::check_result result = _assumptions.empty() ? _solver.check() : _solver.check(_assumptions);

#if DPRINT
  cout << "solve result: " << result << endl;
#endif

  switch(result){
    case z3::check_result::unsat:
      _status = UNSATISFIABLE;
      break;
    case z3::check_result::sat:
      _status = SATISFIABLE;
      _model = _solver.get_model();
#if DPRINT
      cout << "model : " << endl;
      for(unsigned i=0; i < _model.size(); i++){
        z3::func_decl v = _model[i];
        cout << v.name() << " = " << _model.get_const_interp(v) << endl;
      }
#endif
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

SATSolver::Status Z3Interfacing::solveUnderAssumptions(const SATLiteralStack& assumps, unsigned conflictCountLimit, bool onlyProperSubusets,bool withGuard)
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
    z3::expr z_assump = getRepresentation(v_assump,withGuard);

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
      vstring cip = vstring(ci.to_string().c_str());
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
  bool named = _namedExpressions.find(var);
  //cout << "named:" << named << endl;
  z3::expr rep = named ? getNameExpr(var) : getRepresentation(SATLiteral(var,1),false);
  //cout << "rep is " << rep << " named was " << named << endl;
  z3::expr assignment = _model.eval(rep,true /*model_completion*/);
  //cout << "ass is " << assignment << endl;


  if(assignment.bool_value()==Z3_L_TRUE){
  //cout << "returning true for " << var << endl;
    return TRUE;
  }
  if(assignment.bool_value()==Z3_L_FALSE){
  //cout << "returning false for " << var << endl;
    return FALSE;
  }

  // with model_completion true (see above), there should be no don't-knows

  ASSERTION_VIOLATION_REP(assignment); // This is actually not a problem for AVATAR in release (see recomputeModel in Splitter.cpp)
  return NOT_KNOWN;
}

enum RecursionMode {
  RM_SCHED_ARGS,
  RM_CREATE_TERM
};


Term* Z3Interfacing::representNumeral(z3::expr &assignment, unsigned srt) {
  bool is_int = assignment.is_int();
  ASS(is_int || assignment.is_real());
  if(is_int){
    ASS(srt == Sorts::SRT_INTEGER);
    int value;
    if (assignment.is_numeral_i(value)) {
      Term* t = theory->representConstant(IntegerConstantType(value));
      // cout << "evaluteInModel: " << trm->toString() <<" has value " << value << endl;
      return t;
    } else {
      return 0;
    }
  }
  else{
    int n;
    int d;
    z3::expr numerator = assignment.numerator();
    z3::expr denominator = assignment.denominator();
    if(!numerator.is_numeral_i(n) || !denominator.is_numeral_i(d)){
      return 0;
    }
    if(srt == Sorts::SRT_RATIONAL){
      Term* t = theory->representConstant(RationalConstantType(n,d));
      return t;
    }
    else{
      ASS(srt == Sorts::SRT_REAL);
      Term* t = theory->representConstant(RealConstantType(RationalConstantType(n,d)));
      return t;
    }
  }
  ASSERTION_VIOLATION;
};

//Term* Z3Interfacing::representArray(z3::expr* expr) {
//};

Term* Z3Interfacing::evaluateInModel(Term* trm)
{
  CALL("Z3Interfacing::evaluateInModel");

  ASS(!trm->isLiteral());

  unsigned srt = SortHelper::getResultSort(trm);
  bool name; //TODO what do we do about naming?
  z3::expr rep = getz3expr(trm,false,name,false);
  z3::expr assignment = _model.eval(rep,true); // true means "model_completion"

  // now translate assignment back into a term!

  /* Recursive algorithm:
     Term* convert(z3::exp exp) {
       if (exp.is_const()) {
          //return constant tranlastion
       } else if (exp.is_app()) {
         Stack<Term*> cargs;
         for (int i=exp.arg_count(); i >= 0; i--) {
           cargs.push(convert(exp));
         }
         head = expr.fun_decl();
         //return term: head(cargs)
       }
     }
   */

  Stack<Term*> subterms;
  Stack<z3::expr*> z3subterms;
  Stack<RecursionMode> modes;

  z3subterms.push(& assignment);
  modes.push(RM_SCHED_ARGS);
  while(z3subterms.isNonEmpty()) {
    z3::expr* el = z3subterms.pop();
    RecursionMode mode = modes.pop();
    switch (mode) {
    case RM_SCHED_ARGS:
      z3subterms.push(el);
      modes.push(RM_CREATE_TERM);
      if (el->is_app()) {
        for (unsigned i=el->num_args(); i>0; i--) {
          z3::expr arg = el->arg(i-1);
          z3subterms.push(&arg);
          modes.push(RM_SCHED_ARGS);
        }
      }
      break;
    case RM_CREATE_TERM:
      //TODO: create term
      break;
    default:
      ASSERTION_VIOLATION;
    }
  }

  // For now just deal with the case where it is an integer
  if(assignment.is_numeral()){
    representNumeral(assignment, srt);
  } else {
    if (assignment.is_array()) {
#if DPRINT
      cerr << "evaluating array assignment for " << rep << " = " << assignment << endl;
      cerr << assignment.is_const() << " : " << assignment.is_app()
           << " : " << assignment.num_args()
           << " : " << assignment.decl()
           << " : " << assignment.decl().is_const() << endl;
      for (unsigned int i=0; i < assignment.num_args(); i++) {
        cerr << assignment.arg(i);
      }
      cerr << endl;
      z3::func_decl f = assignment.decl();
    // TODO: implement
#endif
    } else {
      // TODO" assignment such as "(root-obj (+ (^ x 2) (- 128)) 1)" is an algebraic number, but not a numeral
      // would be interesting to allow such Sorts::SRT_REAL things to live in vampire
      // of course, they are not in general Sorts::SRT_RATIONAL
#if DPRINT
    cerr << "no model evaluation for " << rep << endl;
#endif
    }
  }

  return 0;
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
  if(env.sorts->isOfStructuredSort(s,Sorts::StructuredSort::ARRAY)){
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
z3::expr Z3Interfacing::getz3expr(Term* trm,bool isLit,bool&nameExpression,bool withGuard)
{
  CALL("Z3Interfacing::getz3expr");
  BYPASSING_ALLOCATOR;
  ASS(trm);
  ASS(trm->ground());

#if DPRINT
  cout << "getz3expr of " << trm->toString() << endl;
#endif

    Signature::Symbol* symb;
    unsigned range_sort;
    OperatorType* type;
    bool is_equality = false;
    if(isLit){
      symb = env.signature->getPredicate(trm->functor());
      OperatorType* ptype = symb->predType();
      type = ptype;
      range_sort = Sorts::SRT_BOOL;
      // check for equality
      if(trm->functor()==0){
         is_equality=true;
         ASS(trm->arity()==2);
      }
    }else{
      symb = env.signature->getFunction(trm->functor());
      OperatorType* ftype = symb->fnType();
      type = ftype;
      range_sort = ftype->result();
    }

    //if constant treat specially
    if(trm->arity()==0){
      if(symb->integerConstant()){
        IntegerConstantType value = symb->integerValue();
        return _context.int_val(value.toInner());
      }
      if(symb->realConstant()){
        RealConstantType value = symb->realValue();
        return _context.real_val(value.numerator().toInner(),value.denominator().toInner());
      }
      if(symb->rationalConstant()){
        RationalConstantType value = symb->rationalValue();
        return _context.real_val(value.numerator().toInner(),value.denominator().toInner());
      }
      if(!isLit && env.signature->isFoolConstantSymbol(true,trm->functor())){
        return _context.bool_val(true);
      }
      if(!isLit && env.signature->isFoolConstantSymbol(false,trm->functor())){
        return _context.bool_val(false);
      }
      if (symb->overflownConstant()) {
        // too large for native representation, but z3 should cope

        switch (symb->fnType()->result()) {
        case Sorts::SRT_INTEGER:
          return _context.int_val(symb->name().c_str());
        case Sorts::SRT_RATIONAL:
          return _context.real_val(symb->name().c_str());
        case Sorts::SRT_REAL:
          return _context.real_val(symb->name().c_str());
        default:
          ;
          // intentional fallthrough; the input is fof (and not tff), so let's just treat this as a constant
        }
      }

      // If not value then create constant symbol
      //cout << "HERE " << env.sorts->sortName(range_sort) << " for " << symb->name() << endl; 
      return getNameConst(symb->name(),getz3sort(range_sort));
    }
    ASS(trm->arity()>0);

    // Next translate term arguments
    //IMPORTANT - every push_back to args must be matched by a pop_back
    // note that the z3 functions do this already
    z3::expr_vector args = z3::expr_vector(_context);
    for(unsigned i=0;i<trm->arity();i++){
      TermList* arg = trm->nthArgument(i);
      ASS(!arg->isVar());// Term should be ground
      args.push_back(getz3expr(arg->term(),false,nameExpression,withGuard));
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

      if(Theory::isPolymorphic(interp)){
        nameExpression = true;
        switch(interp){
          case Theory::ARRAY_SELECT:
          case Theory::ARRAY_BOOL_SELECT:
            // select(array,index)
            ret = select(args[0],args[1]);
            break;

          case Theory::ARRAY_STORE:
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
        case Theory::INT_DIVIDES:
          if(withGuard){addIntNonZero(args[0]);}
          //cout << "SET name=true" << endl;
          nameExpression = true;
          ret = z3::mod(args[1], args[0]) == _context.int_val(0);
          break;

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

        // Don't really need as it's preprocessed away
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

        case Theory::RAT_QUOTIENT:
        case Theory::REAL_QUOTIENT:
          if(withGuard){addRealNonZero(args[1]);}
          ret= args[0] / args[1];
          break;

        case Theory::INT_QUOTIENT_E: 
          if(withGuard){addIntNonZero(args[1]);}
          ret= args[0] / args[1];
          break;

        // The z3 header must be wrong
        //case Theory::RAT_QUOTIENT_E: 
        //case Theory::REAL_QUOTIENT_E: 
           //TODO

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

        case Theory::INT_ABS:
          {
            z3::expr t = args[0];
            ret = ite(t > 0, t, -t);
            break;
          }

         case Theory::INT_QUOTIENT_T:
         case Theory::INT_REMAINDER_T:
           if(withGuard){addIntNonZero(args[1]);}
           // leave as uninterpreted
           addTruncatedOperations(args,Theory::INT_QUOTIENT_T,Theory::INT_REMAINDER_T,range_sort);
           skip=true;
           break;
         case Theory::RAT_QUOTIENT_T:
           if(withGuard){addRealNonZero(args[1]);}
           ret = truncate(args[0]/args[1]);
           addTruncatedOperations(args,Theory::RAT_QUOTIENT_T,Theory::RAT_REMAINDER_T,range_sort);
           break;
         case Theory::RAT_REMAINDER_T:
           if(withGuard){addRealNonZero(args[1]);}
           skip=true;
           addTruncatedOperations(args,Theory::RAT_QUOTIENT_T,Theory::RAT_REMAINDER_T,range_sort);
           break;
         case Theory::REAL_QUOTIENT_T:
           if(withGuard){addRealNonZero(args[1]);}
           ret = truncate(args[0]/args[1]);
           addTruncatedOperations(args,Theory::REAL_QUOTIENT_T,Theory::REAL_REMAINDER_T,range_sort);
           break;
         case Theory::REAL_REMAINDER_T:
           if(withGuard){addRealNonZero(args[1]);}
           skip=true;
           addTruncatedOperations(args,Theory::REAL_QUOTIENT_T,Theory::REAL_REMAINDER_T,range_sort);
           break;

         case Theory::INT_QUOTIENT_F:
         case Theory::INT_REMAINDER_F:
           if(withGuard){addIntNonZero(args[1]);}
           // leave as uninterpreted
           addFloorOperations(args,Theory::INT_QUOTIENT_F,Theory::INT_REMAINDER_F,range_sort);
           skip=true;
           break;
         case Theory::RAT_QUOTIENT_F:
           if(withGuard){addRealNonZero(args[1]);}
           ret = to_real(to_int(args[0] / args[1]));
           addFloorOperations(args,Theory::RAT_QUOTIENT_F,Theory::RAT_REMAINDER_F,range_sort);
           break;
         case Theory::RAT_REMAINDER_F:
           if(withGuard){addRealNonZero(args[1]);}
           skip=true;
           addFloorOperations(args,Theory::RAT_QUOTIENT_F,Theory::RAT_REMAINDER_F,range_sort);
           break;
         case Theory::REAL_QUOTIENT_F:
           if(withGuard){addRealNonZero(args[1]);}
           ret = to_real(to_int(args[0] / args[1]));
           addFloorOperations(args,Theory::REAL_QUOTIENT_F,Theory::REAL_REMAINDER_F,range_sort);
           break;
         case Theory::REAL_REMAINDER_F:
           if(withGuard){addRealNonZero(args[1]);}
           skip=true;
           addFloorOperations(args,Theory::REAL_QUOTIENT_F,Theory::REAL_REMAINDER_F,range_sort);
           break;

         case Theory::RAT_REMAINDER_E:
         case Theory::REAL_REMAINDER_E:
           if(withGuard){addRealNonZero(args[1]);}
           nameExpression = true; 
           ret = z3::mod(args[0], args[1]);
           break;

         case Theory::INT_REMAINDER_E:
           if(withGuard){addIntNonZero(args[1]);}
           nameExpression = true;
           ret = z3::mod(args[0], args[1]);
           break;

       // Numerical comparisons
       // is_rat and to_rat not supported

       case Theory::INT_IS_INT:
       case Theory::RAT_IS_INT:
       case Theory::REAL_IS_INT:
         ret = z3::is_int(args[0]);
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
          if(withGuard){
            throw UninterpretedForZ3Exception();
          }
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

z3::expr Z3Interfacing::getRepresentation(SATLiteral slit,bool withGuard)
{
  CALL("Z3Interfacing::getRepresentation");
  BYPASSING_ALLOCATOR;

  //cout << "slit: " << slit.toString() << endl;

  //First, does this represent a ground literal
  Literal* lit = sat2fo.toFO(slit);
  if(lit && lit->ground()){
    //cout << "getRepresentation of " << lit->toString() << endl;
    // Now translate it into an SMT object 
    try{
      // TODO everything is being named!!
      bool nameExpression = true;
      z3::expr e = getz3expr(lit,true,nameExpression,withGuard);
      cout << "got rep " << e << endl;

      if(nameExpression && _namedExpressions.insert(slit.var())) {
        z3::expr bname = getNameExpr(slit.var()); 
        //cout << "Naming " << e << " as " << bname << endl;
        z3::expr naming = (bname == e);
        _solver.add(naming);
  if(_showZ3){
    env.beginOutput();
    env.out() << "[Z3] add (naming): " << naming << std::endl;
    env.endOutput();
  }
      }

      if(slit.isNegative()){ e = !e;}
      return e;
    }catch(z3::exception& exception){
     reportSpiderFail();
     //cout << "Z3 exception:\n" << exception.msg() << endl;
     ASSERTION_VIOLATION_REP("Failed to create Z3 rep for " + lit->toString());
    }
  }
  //if non ground then just create a propositional variable
  z3::expr e = getNameExpr(slit.var()); 
  if(slit.isNegative()) return !e;
  else return e;
}

SATClause* Z3Interfacing::getRefutation() {

    if(!_unsatCoreForRefutations)
      return PrimitiveProofRecordingSATSolver::getRefutation(); 

    ASS_EQ(_solver.check(),z3::check_result::unsat);

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
        z3::expr e = getRepresentation(l,false); 
        z3clause = z3clause || e;
      }
      vstring p = ps+Int::toString(n++);
      //cout << p << ": " << cl->toString() << endl;
      solver.add(z3clause,p.c_str());
      lookup.insert(p,cl);
    }
  
    z3::check_result result = solver.check();
    ASS_EQ(result,z3::check_result::unsat);   // the new version of Z3 does not suppot unsat-cores?
  
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

void Z3Interfacing::addIntNonZero(z3::expr t)
{
  CALL("Z3Interfacing::addIntNonZero");

   z3::expr zero = _context.int_val(0);

  _solver.add(t != zero);
}

void Z3Interfacing::addRealNonZero(z3::expr t)
{
  CALL("Z3Interfacing::addRealNonZero");

   z3::expr zero = _context.real_val(0);
   z3::expr side = t!=zero;
  if(_showZ3){
    env.beginOutput();
    env.out() << "[Z3] add (RealNonZero): " << side << std::endl;
    env.endOutput();
  }
  _solver.add(side);
}

/**
 * Add axioms for quotient_t and remainder_t that will be treated
 * uninterpreted
 *
 **/
void Z3Interfacing::addTruncatedOperations(z3::expr_vector args, Interpretation qi, Interpretation ti, unsigned srt) 
{
  CALL("Z3Interfacing::addTruncatedOperations");
  
  unsigned qfun = env.signature->getInterpretingSymbol(qi);
  Signature::Symbol* qsymb = env.signature->getFunction(qfun); 
  ASS(qsymb);
  z3::symbol qs = _context.str_symbol(qsymb->name().c_str());
  
  unsigned rfun = env.signature->getInterpretingSymbol(ti);
  Signature::Symbol* rsymb = env.signature->getFunction(rfun);
  z3::symbol rs = _context.str_symbol(rsymb->name().c_str());

  z3::expr e1 = args[0];
  z3::expr e2 = args[1];


  z3::sort_vector domain_sorts = z3::sort_vector(_context);
  domain_sorts.push_back(getz3sort(srt));
  domain_sorts.push_back(getz3sort(srt));

  z3::func_decl r = _context.function(rs,domain_sorts,getz3sort(srt));
  z3::expr r_e1_e2 = r(args);

  if(srt == Sorts::SRT_INTEGER){

    domain_sorts = z3::sort_vector(_context);
    domain_sorts.push_back(getz3sort(srt));
    domain_sorts.push_back(getz3sort(srt));
    z3::func_decl q = _context.function(qs,domain_sorts,getz3sort(srt));
    z3::expr_vector qargs = z3::expr_vector(_context);
    qargs.push_back(e1);
    qargs.push_back(e2);
    z3::expr q_e1_e2 = q(qargs);

    // e1 >= 0 & e2 > 0 -> e2 * q(e1,e2) <= e1 & e2 * q(e1,e2) > e1 - e2
    z3::expr one = implies(( (e1 >= 0) && (e2 > 0) ), ( ( (e2*q_e1_e2) <= e1) && ( (e2*q_e1_e2) > (e1-e2) ) ) );
    _solver.add(one);

    // e1 >= 0 & e2 < 0 -> e2 * q(e1,e2) <= e1 & e2 * q(e1,e2) > e1 + e2
    z3::expr two = implies(( (e1 >=0) && (e2 <0) ), ( (e2*q_e1_e2) <= e1) && ( (e2*q_e1_e2) > (e1+e2) ) );
    _solver.add(two);

    // e1 < 0 & e2 > 0 -> e2 * q(e1,e2) >= e1 & e2 * q(e1,e2) < e1 + e2
    z3::expr three = implies( ((e1<0) && (e2>0)), ( ( (e2*q_e1_e2) >= e1 ) && ( (e2*q_e1_e2) < (e1+e2) ) ) );
    _solver.add(three);

    // e1 < 0 & e2 < 0 -> e2 * q(e1,e2) >= e1 & e2 * q(e1,e2) < e1 - e2
    z3::expr four = implies( ((e1<0) && (e2<0)), ( ((e2*q_e1_e2) >= e1) && ( (e2*q_e1_e2) < (e1-e2) ) ) ); 
    _solver.add(four);

    // e2 != 0 -> e2 * q(e1,e2) + r(e1,e2) = e1
    z3::expr five = implies( (e2!=0), ( ((e2*q_e1_e2)+ r_e1_e2) == e1 ) );
    _solver.add(five);
  }
  else{
    // e2 != 0 -> e2 * q(e1,e2) + r(e1,e2) = e1
    z3::expr five = implies( (e2!=0), ( ((e2*truncate(e1/e2))+ r_e1_e2) == e1 ) );
    _solver.add(five);
  }
}
/**
 *
 **/ 
void Z3Interfacing::addFloorOperations(z3::expr_vector args, Interpretation qi, Interpretation ti, unsigned srt)
{
  CALL("Z3Interfacing::addFloorOperations");

  unsigned qfun = env.signature->getInterpretingSymbol(qi);
  Signature::Symbol* qsymb = env.signature->getFunction(qfun);
  z3::symbol qs = _context.str_symbol(qsymb->name().c_str());

  unsigned rfun = env.signature->getInterpretingSymbol(ti);
  Signature::Symbol* rsymb = env.signature->getFunction(rfun);
  z3::symbol rs = _context.str_symbol(rsymb->name().c_str());

  z3::expr e1 = args[0];
  z3::expr e2 = args[1];

  z3::sort_vector domain_sorts = z3::sort_vector(_context);
  domain_sorts.push_back(getz3sort(srt));
  domain_sorts.push_back(getz3sort(srt));

  z3::func_decl r = _context.function(rs,domain_sorts,getz3sort(srt));
  z3::expr r_e1_e2 = r(args);

  if(srt == Sorts::SRT_INTEGER){

    domain_sorts = z3::sort_vector(_context);
    domain_sorts.push_back(getz3sort(srt));
    domain_sorts.push_back(getz3sort(srt));
    z3::func_decl q = _context.function(qs,domain_sorts,getz3sort(srt));
    z3::expr_vector qargs = z3::expr_vector(_context);
    qargs.push_back(e1);
    qargs.push_back(e2);
    z3::expr q_e1_e2 = q(qargs);

    // e2 != 0 -> e2*q(e1,e2) <= e1 & e2*q(e1,e2) > e1 - e2 
    z3::expr one = implies( (e2!=0), ( ((e2*q_e1_e2) <= e1) && ((e2*q_e1_e2) > (e1-e2) ) ) );
     _solver.add(one);

    // e2 != 0 -> e2 * q(e1,e2) + r(e1,e2) = e1
    z3::expr five = implies( (e2!=0), ( ((e2*q_e1_e2)+ r_e1_e2) == e1 ) );
    _solver.add(five);
  }
  else{
    // e2 != 0 -> e2 * q(e1,e2) + r(e1,e2) = e1
    z3::expr five = implies( (e2!=0), ( ((e2*to_real(to_int(e1/e2)))+ r_e1_e2) == e1 ) );
    _solver.add(five);
  }

}


} // namespace SAT

#endif /** if VZ3 **/
