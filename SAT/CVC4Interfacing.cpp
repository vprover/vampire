
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
  
CVC4Interfacing::CVC4Interfacing(const Shell::Options& opts,SAT2FO& s2f):
   _engine(&_manager), _showCVC4(true),

  _varCnt(0), sat2fo(s2f), _status(SATISFIABLE),

  _unsatCoreForRefutations(opts.z3UnsatCores())
{
  CALL("CVC4Interfacing::CVC4Interfacing");

  _engine.setOption("incremental", true);
  _engine.setOption("produce-models", true);
  _engine.setOption("e-matching", false);
}
  
unsigned CVC4Interfacing::newVar()
{
  CALL("CVC4Interfacing::newVar");
  BYPASSING_ALLOCATOR;

  _varCnt++;

  CVC4::Expr expr = createRepresentation(_varCnt);
  CVC4::Expr name = createFreshExprName(_varCnt);

  CVC4::Expr namingAxiom = _manager.mkExpr(CVC4::kind::EQUAL, expr, name);
  if(_showCVC4) {
    env.beginOutput();
    env.out() << "[CVC4] add naming axiom: " << namingAxiom << std::endl;
    env.endOutput();
  }
  _engine.assertFormula(namingAxiom);

  ALWAYS(_representations.insert(_varCnt,name)); // we store the name, not the actual expr!

  return _varCnt;
}

CVC4::Expr CVC4Interfacing::createRepresentation(unsigned satVar)
{
  CALL("CVC4Interfacing::createRepresentation");

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

    CVC4::Expr e = getRepr(lit,vars);

    ASS(vars.isEmpty());

    if (lit->isNegative()) {
      e = _manager.mkExpr(CVC4::kind::NOT,e);
    }

    return e;
  } else {
    // the non-ground component case
    Clause* cl = sat2fo.lookupComponentClause(satVar);

    if(_showCVC4) {
      env.beginOutput();
      env.out() << "[CVC4] create repr for: " << cl->toString() << std::endl;
      env.endOutput();
    }

    CVC4::Expr cvc4clause = _manager.mkConst(false);

    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      Literal* lit = (*cl)[i];

      CVC4::Expr e = getRepr(lit,vars);

      if (lit->isNegative()) {
        e = _manager.mkExpr(CVC4::kind::NOT,e);
      }

      cvc4clause = _manager.mkExpr(CVC4::kind::OR, cvc4clause, e);
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

      cvc4clause = _manager.mkExpr(CVC4::kind::FORALL, bound_var_list, cvc4clause);
    }

    return cvc4clause;
  }
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
    /*
    if (symb->integerConstant()) {
      IntegerConstantType value = symb->integerValue();
      return _manager.mkConst(CVC4::Integer(value.toInner()));
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
        return _manager.mkConst(CVC4::Integer(symb->name().c_str()));
      case Sorts::SRT_RATIONAL:
        return _manager.mkConst(CVC4::Rational(symb->name().c_str()));
      case Sorts::SRT_REAL:
        return _manager.mkConst(CVC4::Rational(symb->name().c_str()));
      default:
        ;
        // intentional fallthrough; the input is fof (and not tff), so let's just treat this as a constant
      }
    }
    */

    // If not value then create constant symbol

    CVC4::Expr e;
    // we cache constants, because CVC4 likes fresh ones and we don't
    if (!_constants.find(std::make_pair(trm->functor(),range_sort),e)) {
      e = createFreshConst(symb->name(),getCVC4sort(range_sort));
      ALWAYS(_constants.insert(std::make_pair(trm->functor(),range_sort),e));
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
        CVC4::Type varSrt = getCVC4sort(type->arg(i));
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
    } else {

      // TODO !!!

      // but not relevant for the fof AVATAR

    }
  }

  // the uninterpreted symbols and fallthrough from interpreted
  CVC4::Expr theFunction;
  if (!_nonZeroAritySymbols.find(std::make_pair(trm->functor(),range_sort),theFunction)) {
    vector<CVC4::Type> domain_sorts;
    for (unsigned i=0; i<type->arity(); i++) {
      domain_sorts.push_back(getCVC4sort(type->arg(i)));
    }
    CVC4::FunctionType fnType = _manager.mkFunctionType(domain_sorts,getCVC4sort(range_sort));
    theFunction = _manager.mkVar(string(symb->name().c_str()),fnType);

    ALWAYS(_nonZeroAritySymbols.insert(std::make_pair(trm->functor(),range_sort),theFunction));
  }

  return _manager.mkExpr(CVC4::kind::APPLY_UF,theFunction,args);
}

SATClause* CVC4Interfacing::getRefutation() {
  return PrimitiveProofRecordingSATSolver::getRefutation();

  // TODO:: could try doing unsat core stuff
}

} // namespace SAT

