
/*
 * File CVC4Interfacing.cpp.
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
 * @file CVC4Interfacing.cpp
 * Implements class CVC4Interfacing
 */

#if not VZ3

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

#include "CVC4Interfacing.hpp"

namespace SAT
{

using namespace Shell;  
using namespace Lib;  
  
CVC4Interfacing::CVC4Interfacing(const Shell::Options& opts,SAT2FO& s2f, bool withGuard):
    _addingWithGuard(withGuard), _engine(&_manager), _showCVC4(opts.showCVC4()),
   _translateNongnd(opts.cvc4TranslateNonGnd()),

  _varCnt(0), sat2fo(s2f), _status(SATISFIABLE)
{
  CALL("CVC4Interfacing::CVC4Interfacing");

  _engine.setLogic("ALL");

  _engine.setOption("incremental", true);
  _engine.setOption("produce-models", true);
  if (!opts.cvc4WithEMatching()) {
    _engine.setOption("e-matching", false);
  }

  _engine.setOption("symmetry-breaker",false);

  _engine.setOption("decision","internal");

  // _engine.setOption("help",true);

  if (opts.cvc4InstantiationLimit() > 0) {
    _engine.setOption("inst-round-limit",CVC4::SExpr(opts.cvc4InstantiationLimit()));
  }

  if (opts.cvc4InstantiationLimitAll() > 0) {
    _engine.setOption("inst-round-limit-all",CVC4::SExpr(opts.cvc4InstantiationLimitAll()));
  }

  // dumping stuff
  //_engine.setOption("output-language",CVC4::SExpr("smt2"));
  //_engine.setOption("dump",CVC4::SExpr("assertions"));
}
  
unsigned CVC4Interfacing::newVar()
{
  CALL("CVC4Interfacing::newVar");
  BYPASSING_ALLOCATOR;

  _varCnt++;

  CVC4::Expr name = createFreshExprName(_varCnt);
  ALWAYS(_representations.insert(_varCnt,name)); // we store the name, not the actual expr!

  createAndNameRepresentation(_varCnt,name);

  return _varCnt;
}

void CVC4Interfacing::createAndNameRepresentation(unsigned satVar, CVC4::Expr name)
{
  CALL("CVC4Interfacing::createAndNameRepresentation");

  CVC4::Expr repr;

  // ASSUMES sat2fo already has a nice first-order value for us (either ground or non-ground).

  // for collecting variables when translating clauses
  VarMap vars; // cannot be static, since DHMap's reset doesn't destroy Vals and it's too late to destroy them in ~DHMap, because by then _manager could be gone, and that's bad!

  Literal* lit = sat2fo.toFO(SATLiteral(satVar,1)); // annoyingly, we cannot ask sat2fo about the variable directly, so we create a positive literal
  if (lit) {
    // the ground component case
    ASS(lit->ground());

    ASS(lit->isPositive());

    if(_showCVC4) {
      env.beginOutput();
      env.out() << "[CVC4] create repr for: " << lit->toString() << std::endl;
      env.endOutput();
    }

    repr = getRepr(lit,vars);

    ASS(vars.isEmpty());

    if (lit->isNegative()) {
      repr = _manager.mkExpr(CVC4::kind::NOT,repr);
    }
  } else {
    // simply skip, if we don't want translation of non-gnd components
    if (!_translateNongnd) {
      return;
    }

    // the non-ground component case
    Clause* cl = sat2fo.lookupComponentClause(satVar);

    if(_showCVC4) {
      env.beginOutput();
      env.out() << "[CVC4] create repr for: " << cl->toString() << std::endl;
      env.endOutput();
    }

    repr = _manager.mkConst(false);

    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      Literal* lit = (*cl)[i];

      CVC4::Expr e = getRepr(lit,vars);

      if (lit->isNegative()) {
        e = _manager.mkExpr(CVC4::kind::NOT,e);
      }

      repr = _manager.mkExpr(CVC4::kind::OR, repr, e);
    }

    // the universal closure
    if (!vars.isEmpty()) {
      static vector<CVC4::Expr> bound_vars; // here static is fine. vector calls destructors on clear()
      ASS(bound_vars.empty()); // just need to keep it empty between the calls. Capacity can still be allocated.

      VarMap::Iterator it(vars);
      while (it.hasNext()) {
        bound_vars.push_back(it.next());
      }
      CVC4::Expr bound_var_list = _manager.mkExpr(CVC4::kind::BOUND_VAR_LIST, bound_vars);

      bound_vars.clear();

      repr = _manager.mkExpr(CVC4::kind::FORALL, bound_var_list, repr);
    }

  }

  CVC4::Expr namingAxiom = _manager.mkExpr(CVC4::kind::EQUAL, repr, name);
  if(_showCVC4) {
    env.beginOutput();
    env.out() << "[CVC4] add naming axiom: " << namingAxiom << std::endl;
    env.endOutput();
  }
  _engine.assertFormula(namingAxiom);

}

void CVC4Interfacing::addClause(SATClause* cl)
{
  CALL("CVC4Interfacing::addClause");
  BYPASSING_ALLOCATOR;
  ASS(cl);

  // store to later generate the refutation
  PrimitiveProofRecordingSATSolver::addClause(cl);

  CVC4::Expr cvc4clause = _manager.mkConst(false);

  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++){
    SATLiteral l = (*cl)[i];
    CVC4::Expr e = _representations.get(l.var());
    if (l.isNegative()) {
      e = _manager.mkExpr(CVC4::kind::NOT,e);
    }
    cvc4clause = _manager.mkExpr(CVC4::kind::OR, cvc4clause, e);
  }

  if(_showCVC4) {
    env.beginOutput();
    env.out() << "[CVC4] add clause: " << cvc4clause << std::endl;
    env.endOutput();
  }
  _engine.assertFormula(cvc4clause);
}

SATSolver::Status CVC4Interfacing::solve(unsigned conflictCountLimit)
{
  CALL("CVC4Interfacing::solve");
  BYPASSING_ALLOCATOR;

  CVC4::Result result = _engine.checkSat();
  ASS_EQ(result.getType(),CVC4::Result::TYPE_SAT);

  // cout << "CVC4 result: " << result << endl;

  // In CVC4, for the purposes of AVATAR, UNKNOWN should be understood as SAT
  if (result == CVC4::Result(CVC4::Result::UNSAT)) {
    _status = UNSATISFIABLE;
  } else {
    _status = SATISFIABLE;
  }

  return _status;
}

SATSolver::VarAssignment CVC4Interfacing::getAssignment(unsigned var)
{
  CALL("CVC4Interfacing::getAssignment");
  BYPASSING_ALLOCATOR;

  ASS_EQ(_status,SATISFIABLE);

  CVC4::Expr e = _representations.get(var);

  CVC4::Expr val = _engine.getValue(e);

  // cout << "expr: " << e << " has value: " << val << endl;

  if (val == _manager.mkConst(true)) {
    return TRUE;
  }
  if (val == _manager.mkConst(false)) {
    return FALSE;
  }

  ASSERTION_VIOLATION;

  cout << "expr: " << e << " has value: " << val << endl;

  return DONT_CARE;
}

CVC4::Type CVC4Interfacing::getCVC4sort(unsigned srt)
{
  CALL("CVC4Interfacing::getCVC4sort");

  CVC4::Type res;
  if (!_sorts.find(srt,res)) {
    if (srt==Sorts::SRT_BOOL) {
      res = _manager.booleanType();
    } else if (srt==Sorts::SRT_INTEGER) {
      res = _manager.integerType();
    } else if (srt==Sorts::SRT_RATIONAL || srt==Sorts::SRT_REAL) { // Dropping the notion of rationality of rationals
      res = _manager.realType();
    } else if (env.sorts->isOfStructuredSort(srt,Sorts::StructuredSort::ARRAY)) {

      CVC4::Type index_sort = getCVC4sort(env.sorts->getArraySort(srt)->getIndexSort());
      CVC4::Type value_sort = getCVC4sort(env.sorts->getArraySort(srt)->getInnerSort());

      res = _manager.mkArrayType(index_sort,value_sort);
    } else {
      res = _manager.mkSort(string(Lib::Int::toString(srt).c_str()));
    }
    ALWAYS(_sorts.insert(srt,res));
  }
  return res;
}

CVC4::Expr CVC4Interfacing::getRepr(Term* trm, VarMap& vars)
{
  CALL("CVC4Interfacing::getRepr");

  // get the signature stuff
  Signature::Symbol* symb;
  unsigned range_sort;
  OperatorType* type;
  bool is_equality = false;
  if (trm->isLiteral()) {
    symb = env.signature->getPredicate(trm->functor());
    type = symb->predType();
    range_sort = Sorts::SRT_BOOL;
    // check for equality
    if(trm->functor()==0){
       is_equality=true;
       ASS(trm->arity()==2);
    }
  } else {
    symb = env.signature->getFunction(trm->functor());
    type = symb->fnType();
    range_sort = type->result();
  }

  // constants first
  if (trm->arity()==0) {
    if (env.signature->isFoolConstantSymbol(true,trm->functor())) {
      return _manager.mkConst(true);
    }
    if (env.signature->isFoolConstantSymbol(false,trm->functor())) {
      return _manager.mkConst(false);
    }
    if (symb->integerConstant()) {
      IntegerConstantType value = symb->integerValue();
      return _manager.mkConst(CVC4::Rational(value.toInner(),1));  // treating ints as rationals with denominator=1
    }
    if (symb->realConstant()) {
      RealConstantType value = symb->realValue();
      return _manager.mkConst(CVC4::Rational(value.numerator().toInner(),value.denominator().toInner()));
    }
    if (symb->rationalConstant()) {
      RationalConstantType value = symb->rationalValue();
      return _manager.mkConst(CVC4::Rational(value.numerator().toInner(),value.denominator().toInner()));
    }
    if (symb->overflownConstant()) {
      // too large for native representation, but cvc4 should cope

      switch (symb->fnType()->result()) {
      case Sorts::SRT_INTEGER:
        return _manager.mkConst(CVC4::Rational(symb->name().c_str()));  // this should work for ints as well!
      case Sorts::SRT_RATIONAL:
        return _manager.mkConst(CVC4::Rational(symb->name().c_str()));
      case Sorts::SRT_REAL:
        return _manager.mkConst(CVC4::Rational(symb->name().c_str()));
      default:
        ;
        // intentional fallthrough; the input is fof (and not tff), so let's just treat this as a constant
      }
    }

    // If not value then create constant symbol

    CVC4::Expr e;
    // we cache constants, because CVC4 likes fresh ones and we don't
    auto const_key = std::make_pair(trm->functor(),range_sort);
    if (!_constants.find(const_key,e)) {
      e = createFreshConst(symb->name(),getCVC4sort(range_sort));
      ALWAYS(_constants.insert(const_key,e));
    }
    return e;
  }

  ASS(trm->arity()>0);

  // Next translate term arguments
  // care about variables!
  vector<CVC4::Expr> args; // this cannot be static (since we recurse)
  for (unsigned i=0; i<trm->arity(); i++) {
    TermList* arg = trm->nthArgument(i);

    CVC4::Expr e;

    if (arg->isVar()) {
      unsigned var = arg->var();
      if (!vars.find(var,e)) {
        vstring varName = "X"+Lib::Int::toString(var);
        CVC4::Type varSrt = getCVC4sort(SortHelper::getArgSort(trm,i));
        e = _manager.mkBoundVar(string(varName.c_str()),varSrt);
        ALWAYS(vars.insert(var,e));
      }
    } else {
      e = getRepr(arg->term(),vars);
    }

    args.push_back(e);
  }

  // now the actual operation

  if (is_equality) { // equality
    return _manager.mkExpr(CVC4::kind::EQUAL,args);
  }

  if (symb->interpreted()) {
    Interpretation interp = static_cast<Signature::InterpretedSymbol*>(symb)->getInterpretation();

    if (Theory::isPolymorphic(interp)) {
      switch (interp) {
        case Theory::ARRAY_SELECT:
        case Theory::ARRAY_BOOL_SELECT:
          // select(array,index)
          return _manager.mkExpr(CVC4::kind::SELECT,args);

        case Theory::ARRAY_STORE:
          // store(array,index,value)
          return _manager.mkExpr(CVC4::kind::STORE,args);

        default:
          break; // will be treated as uninterpreted
      }
    } else { // non-polymorphic ones
      switch(interp) {
        case Theory::INT_DIVIDES: {
          if (_addingWithGuard) { addNeqZero(args[0]); }
          CVC4::Expr modulus = _manager.mkExpr(CVC4::kind::INTS_MODULUS,args[1],args[0]);
          CVC4::Expr zero = _manager.mkConst(CVC4::Rational(0,1));
          return _manager.mkExpr(CVC4::kind::EQUAL,modulus,zero);
        }

        case Theory::INT_UNARY_MINUS:
        case Theory::RAT_UNARY_MINUS:
        case Theory::REAL_UNARY_MINUS:
          return _manager.mkExpr(CVC4::kind::UMINUS,args[0]);

        case Theory::INT_PLUS:
        case Theory::RAT_PLUS:
        case Theory::REAL_PLUS:
          return _manager.mkExpr(CVC4::kind::PLUS,args);

        case Theory::INT_MINUS:
        case Theory::RAT_MINUS:
        case Theory::REAL_MINUS:
          ASSERTION_VIOLATION_REP("Binary minus should have been pre-processed away!");
          break; // take it uninterpreted in release

        case Theory::INT_MULTIPLY:
        case Theory::RAT_MULTIPLY:
        case Theory::REAL_MULTIPLY:
          return _manager.mkExpr(CVC4::kind::MULT,args);

        case Theory::RAT_QUOTIENT:
        case Theory::REAL_QUOTIENT:
          if (_addingWithGuard) { addNeqZero(args[1]); }
          return _manager.mkExpr(CVC4::kind::DIVISION,args);

        case Theory::INT_QUOTIENT_E:
          if (_addingWithGuard) { addNeqZero(args[1]); }
          return _manager.mkExpr(CVC4::kind::INTS_DIVISION,args);

        case Theory::RAT_TO_INT:
        case Theory::REAL_TO_INT:
        case Theory::INT_FLOOR:
        case Theory::RAT_FLOOR:
        case Theory::REAL_FLOOR:
          // int is a subtype of real in cvc4
          return floor(args[0]);

        case Theory::INT_TO_REAL:
        case Theory::RAT_TO_REAL:
        case Theory::INT_TO_RAT:
          // noop as int is a subtype of real in cvc4
          return args[0];

        case Theory::INT_CEILING:
        case Theory::RAT_CEILING:
        case Theory::REAL_CEILING:
          return ceiling(args[0]);

        case Theory::INT_TRUNCATE:
        case Theory::RAT_TRUNCATE:
        case Theory::REAL_TRUNCATE:
          return truncate(args[0]);

        case Theory::INT_ROUND:
        case Theory::RAT_ROUND:
        case Theory::REAL_ROUND:
          return round(args[0]);

        case Theory::INT_ABS:
          return _manager.mkExpr(CVC4::kind::ABS,args[0]);

        // skipping (for now) all the (TPTP-specific) operations for which Z3Interfacing calls addTruncatedOperations/addFloorOperations
        // Note that should we have add*Operations here, there might be some extra challenges connected
        // to the presence of first-order variables in the created "axioms"

        case Theory::RAT_REMAINDER_E:
        case Theory::REAL_REMAINDER_E:
          // wtf are these? Not even TPTP talks about these!
          ASSERTION_VIOLATION;
        case Theory::INT_REMAINDER_E:
          if (_addingWithGuard) { addNeqZero(args[1]); }
          return _manager.mkExpr(CVC4::kind::INTS_MODULUS,args);

        case Theory::INT_IS_INT:
        case Theory::RAT_IS_INT:
        case Theory::REAL_IS_INT:
          return _manager.mkExpr(CVC4::kind::IS_INTEGER,args);

        case Theory::INT_LESS:
        case Theory::RAT_LESS:
        case Theory::REAL_LESS:
          return _manager.mkExpr(CVC4::kind::LT,args);

        case Theory::INT_GREATER:
        case Theory::RAT_GREATER:
        case Theory::REAL_GREATER:
          return _manager.mkExpr(CVC4::kind::GT,args);

        case Theory::INT_LESS_EQUAL:
        case Theory::RAT_LESS_EQUAL:
        case Theory::REAL_LESS_EQUAL:
          return _manager.mkExpr(CVC4::kind::LEQ,args);

        case Theory::INT_GREATER_EQUAL:
        case Theory::RAT_GREATER_EQUAL:
        case Theory::REAL_GREATER_EQUAL:
          return _manager.mkExpr(CVC4::kind::GEQ,args);

        default:
          if (_addingWithGuard) {
            throw UninterpretedForSMTException();
          }
          break; // treat as uninterpreted
      }
    }
  }

  // the uninterpreted symbols and fallthrough from interpreted
  CVC4::Expr theFunction;
  auto fnc_key = std::make_pair(trm->functor(),range_sort);
  if (!_nonZeroAritySymbols.find(fnc_key,theFunction)) {
    vector<CVC4::Type> domain_sorts;
    for (unsigned i=0; i<type->arity(); i++) {
      domain_sorts.push_back(getCVC4sort(type->arg(i)));
    }
    CVC4::FunctionType fnType = _manager.mkFunctionType(domain_sorts,getCVC4sort(range_sort));
    theFunction = _manager.mkVar(string(symb->name().c_str()),fnType);

    ALWAYS(_nonZeroAritySymbols.insert(fnc_key,theFunction));
  }

  return _manager.mkExpr(CVC4::kind::APPLY_UF,theFunction,args);
}

Term* CVC4Interfacing::evaluateInModel(Term* trm) {
  CALL("CVC4Interfacing::evaluateInModel");

  ASS(!trm->isLiteral());

  ASS(trm->ground());
  static VarMap vars_dummy; // everything should be ground here
  CVC4::Expr rep = getRepr(trm,vars_dummy);
  ASS(vars_dummy.isEmpty());

  CVC4::Expr assignment = _engine.getValue(rep);

  ASS(assignment.isConst());
  auto type = assignment.getType();
  if (type == _manager.integerType()) {
    CVC4::Rational i = assignment.getConst<CVC4::Rational>();

    ASS(i.isIntegral());
    CVC4::Integer ii = i.getNumerator();

    if (ii.fitsSignedInt()) {
      return theory->representConstant(IntegerConstantType(ii.getSignedInt()));
    }
    // else nullptr below
  } else if (type == _manager.realType()) {
    CVC4::Rational r = assignment.getConst<CVC4::Rational>();

    CVC4::Integer n = r.getNumerator();
    CVC4::Integer d = r.getDenominator();

    if (n.fitsSignedInt() && d.fitsSignedInt()) {
      unsigned srt = SortHelper::getResultSort(trm);

      if(srt == Sorts::SRT_RATIONAL){
        return theory->representConstant(RationalConstantType(n.getSignedInt(),d.getSignedInt()));
      } else {
        ASS(srt == Sorts::SRT_REAL);
        auto rat = RationalConstantType(n.getSignedInt(),d.getSignedInt());
        return theory->representConstant(RealConstantType(rat));
      }
    }
  }

  return nullptr;
}

SATClause* CVC4Interfacing::getRefutation() {
  return PrimitiveProofRecordingSATSolver::getRefutation();

  // TODO:: could try doing unsat core stuff
}

} // namespace SAT

#endif /** if not VZ3 **/
