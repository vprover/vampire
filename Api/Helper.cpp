/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Helper.cpp
 * Implements class Helper.
 */

#include "Kernel/SortHelper.hpp"
#include "Kernel/Sorts.hpp"

#include "Parse/TPTP.hpp"

#include "Helper_Internal.hpp"

namespace Api
{

using namespace Kernel;
using namespace Shell;

///////////////////////
// DefaultHelperCore
//


DefaultHelperCore* DefaultHelperCore::instance()
{
  static DefaultHelperCore inst;

  return &inst;
}

vstring DefaultHelperCore::getVarName(Var v) const
{
  CALL("DefaultHelperCore::getVarName");

  return "X"+Int::toString(v);
}

vstring DefaultHelperCore::toString(Kernel::TermList t) const
{
  CALL("DefaultHelperCore::toString(TermList)");

  if(t.isOrdinaryVar()) {
    return getVarName(t.var());
  }
  ASS(t.isTerm());
  return t.term()->toString();
}

/** Get dummy name for function or predicate */
vstring DefaultHelperCore::getDummyName(bool pred, unsigned functor)
{
  CALL("DefaultHelperCore::getDummyName/2");

  Signature::Symbol* sym = pred ?
      env.signature->getPredicate(functor) :
      env.signature->getFunction(functor);

  if(sym->interpreted()) {
    return pred ? env.signature->predicateName(functor) :
	env.signature->functionName(functor);
  }

  if(pred) {
    return "p"+Int::toString(functor);
  }
  else {
    return "f"+Int::toString(functor);
  }
}

/** Get dummy name for function or predicate */
vstring DefaultHelperCore::getDummyName(const Kernel::Term* t)
{
  CALL("DefaultHelperCore::getDummyName/1");

  return getDummyName(t->isLiteral(), t->functor());
}

vstring DefaultHelperCore::getSymbolName(bool pred, unsigned functor) const
{
  if(outputDummyNames()) {
    return getDummyName(pred, functor);
  }
  else {
    if(pred) {
      return env.signature->predicateName(functor);
    }
    else {
      return env.signature->functionName(functor);
    }
  }
}

struct DefaultHelperCore::Var2NameMapper
{
  Var2NameMapper(DefaultHelperCore& a) : aux(a) {}
  DECL_RETURN_TYPE(vstring);
  vstring operator()(unsigned v)
  {
    return aux.getVarName(v);
  }
  DefaultHelperCore& aux;
};

StringIterator DefaultHelperCore::getVarNames(VarList* l)
{
  CALL("DefaultHelperCore::getVarNames");

  VirtualIterator<vstring> res=pvi( getPersistentIterator(
      getMappingIterator(
	  VarList::DestructiveIterator(l),
	  Var2NameMapper(*this))
  ) );

  return StringIterator(res);
}



///////////////////////
// FBHelperCore
//


/** build a term f(*args) with specified @b arity */
Term FBHelperCore::term(const Function& f,const Term* args, unsigned arity)
{
  CALL("FBHelperCore::term");

  for(unsigned i = 0; i < arity; i++){
    if(!args[i].isValid()){
      throw ApiException("Attempting to use a term created prior to a solver reset");
    }
  }

  if(!f.isValid()){
    throw ApiException("Attempting to use a function created prior to a solver reset");        
  }
  if(f>=static_cast<unsigned>(env.signature->functions())) {
    throw FormulaBuilderException("Function does not exist");
  }
  if(arity!=env.signature->functionArity(f)) {
    throw FormulaBuilderException("Invalid function arity: "+env.signature->functionName(f));
  }
  ensureArgumentsSortsMatch(env.signature->getFunction(f)->fnType(), args);

  DArray<TermList> argArr;
  argArr.initFromArray(arity, args);

  Term res(Kernel::TermList(Kernel::Term::create(f,arity,argArr.array())));
  res._aux=this; //assign the correct helper object
  return res;
}

/** build a predicate p(*args) with specified @b arity */
Formula FBHelperCore::atom(const Predicate& p, bool positive, const Term* args, unsigned arity)
{
  CALL("FBHelperCore::atom");

  for(unsigned i = 0; i < arity; i++){
    if(!args[i].isValid()){
      throw ApiException("Attempting to use a term created prior to a solver reset");
    }
  }

  if(!p.isValid()){
    throw ApiException("Attempting to use a predicate created prior to a solver reset");        
  }
  if(p>=static_cast<unsigned>(env.signature->predicates())) {
    throw FormulaBuilderException("Predicate does not exist");
  }
  if(arity!=env.signature->predicateArity(p)) {
    throw FormulaBuilderException("Invalid predicate arity: "+env.signature->predicateName(p));
  }
  ensureArgumentsSortsMatch(env.signature->getPredicate(p)->predType(), args);

  DArray<TermList> argArr;
  argArr.initFromArray(arity, args);

  Kernel::Literal* lit=Kernel::Literal::create(p, arity, positive, false, argArr.array());

  Formula res(new Kernel::AtomicFormula(lit));
  res._aux=this; //assign the correct helper object
  return res;
}

unsigned FBHelperCore::getUnaryPredicate()
{
  CALL("FBHelperCore::getUnaryPredicate");

  if(_unaryPredicate!=0) {
    return _unaryPredicate;
  }

  Kernel::Signature& sig = *env.signature;
  unsigned cnt = sig.predicates();
  for(unsigned i=1; i<cnt; i++) {
    if(sig.predicateArity(i)==1 && !sig.getPredicate(i)->interpreted()) {
      _unaryPredicate = i;
      return i;
    }
  }
  _unaryPredicate = sig.addNamePredicate(1);
  return _unaryPredicate;
}

Sort FBHelperCore::getSort(const Api::Term t)
{
  CALL("FBHelperCore::getSort");

  if(t.isVar()) {
    unsigned v = t.var();
    return getVarSort(v);
  }
  else {
    unsigned fun = t.functor();
    return Sort(env.signature->getFunction(fun)->fnType()->result());
  }
}

void FBHelperCore::ensureArgumentsSortsMatch(OperatorType* type, const Api::Term* args)
{
  CALL("FBHelperCore::ensureArgumentsSortsMatch");

  unsigned arity = type->arity();
  for(unsigned i=0; i<arity; i++) {
    unsigned parentSort = type->arg(i);
    Sort argSort = getSort(args[i]);
    if(argSort.isValid() && parentSort!=argSort) {
      throw SortMismatchException("Unexpected sort of term " + args[i].toString());
    }
  }
}

void FBHelperCore::ensureEqualityArgumentsSortsMatch(const Api::Term arg1, const Api::Term arg2)
{
  CALL("FBHelperCore::ensureEqualityArgumentsSortsMatch");

  Sort s1 = getSort(arg1);
  Sort s2 = getSort(arg2);  
  if(s1!=s2) {
    throw SortMismatchException("Different sorts of equality arguments: " + arg1.toString() + " and " + arg2.toString());
  }
}

vstring FBHelperCore::getVarName(Var v) const
{
  CALL("FBHelperCore::getVarName");

  if(outputDummyNames()) {
    return "X"+Int::toString(v);
  }

  vstring res;
  if(varNames.find(v,res)) {
    return res;
  }
  else {
    static bool seen = false;
    if(!seen) {
      seen = true;      
    }
    return "X"+Int::toString(v);

//    Map<Var,vstring>::Iterator it(varNames);
//    while(it.hasNext()) {
//      vstring v;
//      unsigned k;
//      it.next(k,v);
//      cout<<k<<" "<<v<<endl;
//    }
//    throw FormulaBuilderException("Var object was used in FormulaBuilder object which did not create it");
  }
}

Sort FBHelperCore::getVarSort(Var v) const
{
  CALL("FBHelperCore::getVarSort");

  Sort res;
  if(varSorts.find(v,res)) {
    return res;
  }
  else {   
    return Sort::getInvalid();
//    throw FormulaBuilderException("Var object was used in FormulaBuilder object which did not create it");
  }
}

unsigned FBHelperCore::getVar(vstring varName, Sort varSort)
{
  if(_checkNames) {
    if(!isupper(varName[0])) {
      throw InvalidTPTPNameException("Variable name must start with an uppercase character", varName);
    }
    //TODO: add further checks
  }
  
  unsigned res=vars.insert(varName, nextVar);
  if(res==nextVar) {
    nextVar++;
    varNames.insert(res, varName);
    varSorts.insert(res, varSort);
  }
  else {
    Sort oldSort = varSorts.get(res);
    if(!oldSort.isValid()) {
      if(varSort.isValid()) {
	varSorts.replace(res, varSort);
      }
    }
    else {
      if(varSort.isValid() && oldSort!=varSort) {
	throw FormulaBuilderException("Existing variable with different sort requested");
      }
    }
  }
  ASS_L(res, nextVar);
  return res;
}

void FBHelperCore::addAttribute(AttribStack& stack, vstring name, vstring value)
{
  CALL("FBHelperCore::addAttribute");

  AttribPair attr(name,value);
  //TODO: This causes quadratic complexity in the number of attributes
  if(stack.find(attr)) {
    return;
  }
  stack.push(attr);
}


/**
 * Return an alias variable for variable number @b var
 */
unsigned FBHelperCore::FBVarFactory::getVarAlias(unsigned var)
{
  CALL("FBHelperCore::FBVarFactory::getVarAlias");

  vstring origName=_parent.getVarName(var);
  int i=0;
  vstring name;
  do {
    i++;
    name=origName+"_"+Int::toString(i);
  } while(_parent.vars.find(name));

  return _parent.getVar(name, _parent.getVarSort(var));
}

/**
 * Return name of variable number @b var
 */
vstring FBHelperCore::FBVarFactory::getVarName(unsigned var)
{
  CALL("FBHelperCore::FBVarFactory::getVarName");

  return _parent.getVarName(var);
}


///////////////////////
// ApiHelper
//

ApiHelper::ApiHelper() : _obj(0) {}

ApiHelper::~ApiHelper()
{
  CALL("ApiHelper::~ApiHelper");

  updRef(false);
}

ApiHelper::ApiHelper(const ApiHelper& h)
{
  CALL("ApiHelper::ApiHelper(ApiHelper&)");

  _obj=h._obj;
  updRef(true);
}

ApiHelper& ApiHelper::operator=(const ApiHelper& h)
{
  const_cast<ApiHelper&>(h).updRef(true);
  updRef(false);
  _obj=h._obj;
  return *this;
}

ApiHelper& ApiHelper::operator=(FBHelperCore* hc)
{
  hc->incRef();
  updRef(false);
  _obj=hc;
  return *this;
}

void ApiHelper::updRef(bool inc)
{
  CALL("ApiHelper::updRef");

  if(_obj) {
    if(inc) {
      _obj->incRef();
    }
    else {
      _obj->decRef();
    }
  }
}

bool ApiHelper::operator==(const ApiHelper& h) const
{
  CALL("ApiHelper::operator==");

  return _obj==h._obj;
}

bool ApiHelper::operator!=(const ApiHelper& h) const
{
  CALL("ApiHelper::operator!=");

  return _obj!=h._obj;
}

DefaultHelperCore* ApiHelper::operator->() const
{
  CALL("ApiHelper::operator->");

  return **this;
}

DefaultHelperCore* ApiHelper::operator*() const
{
  CALL("ApiHelper::operator*");

  if(_obj) {
    return _obj;
  }
  else {
    return DefaultHelperCore::instance();
  }
}

///////////////////////
// FBHelper
//


FBHelper::FBHelper()
{
  CALL("FBHelper::FBHelper");

  _obj=new FBHelperCore;
  updRef(true);
}

void FBHelper::resetCore()
{
  CALL("FBHelper::resetCore");
  
  _obj->declareInvalid();
  updRef(false);

  _obj=new FBHelperCore;
  updRef(true);  
}

FBHelperCore* FBHelper::operator->() const
{
  CALL("FBHelper::operator->");

  ASS(_obj);
  return _obj;
}


}
