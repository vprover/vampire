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
 * @file FormulaBuilder.cpp
 * Implements class FormulaBuilder.
 */

#include "FormulaBuilder.hpp"

#include "Helper_Internal.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Map.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Parse/TPTP.hpp"

#include "Shell/Options.hpp"
#include "Shell/FOOLElimination.hpp"
#include "Shell/TPTPPrinter.hpp"



using namespace std;
using namespace Lib;
using namespace Shell;

namespace Api
{

FormulaBuilder::FormulaBuilder(bool checkNames, bool checkBindingBoundVariables,
    bool allowImplicitlyTypedVariables, bool outputDummyNames)
{
  CALL("FormulaBuilder::FormulaBuilder");

  _aux->_checkNames=checkNames;
  _aux->_checkBindingBoundVariables=checkBindingBoundVariables;
  _aux->_allowImplicitlyTypedVariables=allowImplicitlyTypedVariables;
  _aux->_outputDummyNames=outputDummyNames;
}

Sort FormulaBuilder::sort(const vstring& sortName)
{
  CALL("FormulaBuilder::sort");

  bool added = false;
  //false means that it is not an interpreted sort
  unsigned res = env.sorts->addSort(sortName, added, false);
  Sort sort(res);
  sort._aux=_aux;
  return sort;
}

Sort FormulaBuilder::integerSort()
{
  CALL("FormulaBuilder::integerSort");

  return Sort(Sorts::SRT_INTEGER);
}

Sort FormulaBuilder::rationalSort()
{
  CALL("FormulaBuilder::integerSort");

  return Sort(Sorts::SRT_RATIONAL);
}

Sort FormulaBuilder::realSort()
{
  CALL("FormulaBuilder::integerSort");

  return Sort(Sorts::SRT_REAL);
}


Sort FormulaBuilder::defaultSort()
{
  CALL("FormulaBuilder::defaultSort");

  return Sort(Sorts::SRT_DEFAULT);
}

vstring FormulaBuilder::getSortName(Sort s)
{
  CALL("FormulaBuilder::getSortName");
  
  if(!s.isValid()){
    throw ApiException("Solver has been reset. Sort is invalid");    
  }
  return env.sorts->sortName(s);
}

vstring FormulaBuilder::getPredicateName(Predicate p)
{
  CALL("FormulaBuilder::getPredicateName");

  if(!p.isValid()){
    throw ApiException("Solver has been reset. Predicate is invalid");    
  }
  return _aux->getSymbolName(true, p);
}

vstring FormulaBuilder::getFunctionName(Function f)
{
  CALL("FormulaBuilder::getFunctionName");

  if(!f.isValid()){
    throw ApiException("Solver has been reset. Function is invalid");    
  }
  return _aux->getSymbolName(true, f);
}


//TODO invalidate vars on a hard solver reset as well?
vstring FormulaBuilder::getVariableName(Var v)
{
  CALL("FormulaBuilder::getVariableName");

  return _aux->getVarName(v);
}


Var FormulaBuilder::var(const vstring& varName)
{
  CALL("FormulaBuilder::var");

  if(!_aux->_allowImplicitlyTypedVariables) {
    throw FormulaBuilderException("Creating implicitly typed variables is not allowed. Use function "
	"FormulaBuilder::var(const vstring& varName, Sort varSort) instead of "
	"FormulaBuilder::var(const vstring& varName)");
  }

  return var(varName, defaultSort());
}

Var FormulaBuilder::var(const vstring& varName, Sort varSort)
{
  CALL("FormulaBuilder::var");

  return _aux->getVar(varName, varSort);
}

Function FormulaBuilder::function(const vstring& funName,unsigned arity, bool builtIn)
{
  CALL("FormulaBuilder::function/2");

  static DArray<Sort> domainSorts;
  domainSorts.init(arity, defaultSort());
  return function(funName, arity, defaultSort(), domainSorts.array(), builtIn);
}

Function FormulaBuilder::function(const vstring& funName, unsigned arity, Sort rangeSort, Sort* domainSorts, bool builtIn)
{
  CALL("FormulaBuilder::function/4");

  bool added;
  unsigned res = env.signature->addFunction(funName, arity, added);
  Kernel::Signature::Symbol* sym = env.signature->getFunction(res);

  static DArray<unsigned> nativeSorts;
  nativeSorts.initFromArray(arity, domainSorts);

  OperatorType* fnType = OperatorType::getFunctionType(arity, nativeSorts.array(), rangeSort);

  if(added) {
    sym->setType(fnType);
  }
  else {
    if(fnType!=sym->fnType()) {
      throw FormulaBuilderException("Creating function " + sym->name() + " with different type than a previously created function "
	  "of the same name and arity. (This must not happen even across different instances of the FormulaBuilder class.)");
    }
  }
  if(builtIn) {
    sym->markProtected();
  }
  Function fun(res);
  fun._aux=_aux;
  return fun;
}

Function FormulaBuilder::integerConstant(int i)
{
  CALL("FormulaBuilder::integerConstant");

  unsigned fun = env.signature->addIntegerConstant(IntegerConstantType(i));
  Function f(fun);
  f._aux=_aux;
  return Function(f);
}

Function FormulaBuilder::integerConstant(vstring i)
{
  CALL("FormulaBuilder::integerConstant");

  unsigned fun;
  try {
    fun = env.signature->addIntegerConstant(IntegerConstantType(i));
  }
  catch (ArithmeticException) {
    throw FormulaBuilderException("Constant value invalid or does not fit into internal representation: " + i);
  }
  Function f(fun);
  f._aux=_aux;
  return Function(f);
}

Function FormulaBuilder::rationalConstantSymbol(Lib::vstring numerator, Lib::vstring denom)
{
  CALL("FormulaBuilder::rationalConstantSymbol");

  unsigned fun;
  try {
    fun = env.signature->addRationalConstant(RationalConstantType(numerator, denom));
  }
  catch (MachineArithmeticException) {
    throw FormulaBuilderException("An arithmetic exception occured during the creation of constant: " + numerator + "/" + denom);
  } catch (DivByZeroException) {
    throw FormulaBuilderException("The denominator of a rational cannot be 0");    
  }
  Function f(fun);
  f._aux=_aux;
  return Function(f);
}

Function FormulaBuilder::realConstantSymbol(Lib::vstring r)
{
  CALL("FormulaBuilder::realConstantSymbol");

  unsigned fun;
  try {
    fun = env.signature->addRealConstant(RealConstantType(r));
  }
  catch (ArithmeticException) {
    throw FormulaBuilderException("An arithmetic exception occured during the creation of constant " + r);
  }
  Function f(fun);
  f._aux=_aux;
  return Function(f);
}

bool FormulaBuilder::checkNames(){
  CALL("FormulaBuilder::checkNames");
  
  return _aux->_checkNames;
}

void FormulaBuilder::reset(){
  CALL("FormulaBuilder::reset");

  _aux.resetCore();
}

Predicate FormulaBuilder::predicate(const vstring& predName,unsigned arity, bool builtIn)
{
  CALL("FormulaBuilder::predicate/2");

  static DArray<Sort> domainSorts;
  domainSorts.init(arity, defaultSort());
  return predicate(predName, arity, domainSorts.array(), builtIn);
}


Predicate FormulaBuilder::predicate(const vstring& predName, unsigned arity, Sort* domainSorts, bool builtIn)
{
  CALL("FormulaBuilder::predicate/3");

  bool added;
  unsigned res = env.signature->addPredicate(predName, arity, added);

  Kernel::Signature::Symbol* sym = env.signature->getPredicate(res);

  static DArray<unsigned> nativeSorts;
  nativeSorts.initFromArray(arity, domainSorts);

  OperatorType* predType = OperatorType::getPredicateType(arity, nativeSorts.array());
  if(added) {
    sym->setType(predType);
  }
  else {
    if(predType!=sym->predType()) {
      throw FormulaBuilderException("Creating predicate " + sym->name() + " with different type than a previously created predicate "
	  "of the same name and arity. (This must not happen even across different instances of the FormulaBuilder class.)");
    }
  }
  if(builtIn) {
    sym->markProtected();
  }
  Predicate pred(res);
  pred._aux=_aux;
  return pred;
}

Predicate FormulaBuilder::interpretedPredicate(Kernel::Theory::Interpretation interp)
{
  CALL("FormulaBuilder::interpretedPredicate");

  //This function is not exposed to API users, so no need
  //to raise an exception
  ASS(!Theory::isFunction(interp));

  unsigned res = env.signature->getInterpretingSymbol(interp);
  Predicate pred(res);
  pred._aux=_aux;
  return pred;
}

Function FormulaBuilder::interpretedFunction(Kernel::Theory::Interpretation interp)
{
  CALL("FormulaBuilder::interpretedFunction");
  
  //This function is not exposed to API users, so no need
  //to raise an exception
  ASS(Theory::isFunction(interp));

  unsigned res = env.signature->getInterpretingSymbol(interp);
  Function func(res);
  func._aux=_aux;
  return func;
}

void FormulaBuilder::addAttribute(Sort p, vstring name, vstring value)
{
  CALL("FormulaBuilder::addAttribute(Sort,vstring,vstring)");

  FBHelperCore::addAttribute(_aux->getSortAttributes(p), name, value);
}

unsigned FormulaBuilder::attributeCount(Sort p)
{
  CALL("FormulaBuilder::attributeCount(Sort)");

  return _aux->getSortAttributes(p).size();
}

vstring FormulaBuilder::getAttributeName(Sort p, unsigned index)
{
  CALL("FormulaBuilder::getAttributeName(Sort,unsigned)");

  if(index>attributeCount(p)) {
    throw FormulaBuilderException("Attribute index out of bounds");
  }
  return _aux->getSortAttributes(p)[index].first;
}

vstring FormulaBuilder::getAttributeValue(Sort p, unsigned index)
{
  CALL("FormulaBuilder::getAttributeValue(Sort,unsigned)");

  if(index>attributeCount(p)) {
    throw FormulaBuilderException("Attribute index out of bounds");
  }
  return _aux->getSortAttributes(p)[index].second;
}

vstring FormulaBuilder::getAttributeValue(Sort p, vstring attributeName)
{
  CALL("FormulaBuilder::getAttributeValue(Sort,vstring)");

  FBHelperCore::AttribStack::BottomFirstIterator it(_aux->getSortAttributes(p));
  while(it.hasNext()) {
    pair<vstring,vstring> curr = it.next();
    if(curr.first==attributeName) {
      return curr.second;
    }
  }
  throw FormulaBuilderException("Requested attribute does not exist");
}

void FormulaBuilder::addAttribute(Predicate p, vstring name, vstring value)
{
  CALL("FormulaBuilder::addAttribute(Predicate,vstring,vstring)");

  FBHelperCore::addAttribute(_aux->getPredicateAttributes(p), name, value);
}

unsigned FormulaBuilder::attributeCount(Predicate p)
{
  CALL("FormulaBuilder::attributeCount(Predicate)");

  return _aux->getPredicateAttributes(p).size();
}

vstring FormulaBuilder::getAttributeName(Predicate p, unsigned index)
{
  CALL("FormulaBuilder::getAttributeName(Predicate,unsigned)");

  if(index>attributeCount(p)) {
    throw FormulaBuilderException("Attribute index out of bounds");
  }
  return _aux->getPredicateAttributes(p)[index].first;
}

vstring FormulaBuilder::getAttributeValue(Predicate p, unsigned index)
{
  CALL("FormulaBuilder::getAttributeValue(Predicate,unsigned)");

  if(index>attributeCount(p)) {
    throw FormulaBuilderException("Attribute index out of bounds");
  }
  return _aux->getPredicateAttributes(p)[index].second;
}

vstring FormulaBuilder::getAttributeValue(Predicate p, vstring attributeName)
{
  CALL("FormulaBuilder::getAttributeValue(Predicate,vstring)");

  FBHelperCore::AttribStack::BottomFirstIterator it(_aux->getPredicateAttributes(p));
  while(it.hasNext()) {
    pair<vstring,vstring> curr = it.next();
    if(curr.first==attributeName) {
      return curr.second;
    }
  }
  throw FormulaBuilderException("Requested attribute does not exist");
}

void FormulaBuilder::addAttribute(Function p, vstring name, vstring value)
{
  CALL("FormulaBuilder::addAttribute(Function,vstring,vstring)");

  FBHelperCore::addAttribute(_aux->getFunctionAttributes(p), name, value);
}

unsigned FormulaBuilder::attributeCount(Function p)
{
  CALL("FormulaBuilder::attributeCount(Function)");

  return _aux->getFunctionAttributes(p).size();
}

vstring FormulaBuilder::getAttributeName(Function p, unsigned index)
{
  CALL("FormulaBuilder::getAttributeName(Function,unsigned)");

  if(index>attributeCount(p)) {
    throw FormulaBuilderException("Attribute index out of bounds");
  }
  return _aux->getFunctionAttributes(p)[index].first;
}

vstring FormulaBuilder::getAttributeValue(Function p, unsigned index)
{
  CALL("FormulaBuilder::getAttributeValue(Function,unsigned)");

  if(index>attributeCount(p)) {
    throw FormulaBuilderException("Attribute index out of bounds");
  }
  return _aux->getFunctionAttributes(p)[index].second;
}

vstring FormulaBuilder::getAttributeValue(Function p, vstring attributeName)
{
  CALL("FormulaBuilder::getAttributeValue(Function,vstring)");

  FBHelperCore::AttribStack::BottomFirstIterator it(_aux->getFunctionAttributes(p));
  while(it.hasNext()) {
    pair<vstring,vstring> curr = it.next();
    if(curr.first==attributeName) {
      return curr.second;
    }
  }
  throw FormulaBuilderException("Requested attribute does not exist");
}


Term FormulaBuilder::varTerm(const Var& v)
{
  CALL("FormulaBuilder::varTerm");

  Term res(Kernel::TermList(v,false));
  res._aux=_aux; //assign the correct helper object
  return res;
}

Term FormulaBuilder::term(const Function& f,const std::vector<Term>& args)
{
  CALL("FormulaBuilder::term");

  for (const Term& arg : args)
  {
    if(!arg.isValid()){
      throw ApiException("Attempting to use a term created prior to a hard solver reset");    
    }
  }
  return _aux->term(f,args.data(),env.signature->functionArity(f));
}

Formula FormulaBuilder::atom(const Predicate& p, const std::vector<Term>& args, bool positive)
{
  CALL("FormulaBuilder::atom");

  for (const Term& arg : args)
  {
    if(!arg.isValid()){
      throw ApiException("Attempting to use a term created prior to a hard solver reset");    
    }
  }
  return _aux->atom(p,positive, args.data(),env.signature->predicateArity(p));
}

Formula FormulaBuilder::equality(const Term& lhs,const Term& rhs, Sort sort, bool positive)
{
  CALL("FormulaBuilder::equality/4");

  if(lhs.sort()!=sort) {
    throw SortMismatchException("Sorts of equality sides is not as declared");
  }
  return equality(lhs, rhs, positive);
}

Formula FormulaBuilder::equality(const Term& lhs,const Term& rhs, bool positive)
{
  CALL("FormulaBuilder::equality/3");

  if(!lhs.isValid() || !rhs.isValid()){
    throw ApiException("Attempting to build an equality with a term created prior to a hard solver reset"); 
  }

  _aux->ensureEqualityArgumentsSortsMatch(lhs, rhs);
  unsigned srt = lhs.sort();
  if(srt!=rhs.sort()) {
    throw FormulaBuilderException("sort mismatch in equality creation: "+lhs.toString()+" = "+rhs.toString());
  }
  Literal* lit = Kernel::Literal::createEquality(positive, lhs, rhs, srt);
  Formula res(new Kernel::AtomicFormula(lit));
  res._aux=_aux; //assign the correct helper object
  return res;
}

Formula FormulaBuilder::trueFormula()
{
  CALL("FormulaBuilder::trueFormula");

  Formula res(new Kernel::Formula(true));
  res._aux=_aux; //assign the correct helper object
  return res;
}

Formula FormulaBuilder::falseFormula()
{
  CALL("FormulaBuilder::falseFormula");

  Formula res(new Kernel::Formula(false));
  res._aux=_aux; //assign the correct helper object
  return res;
}

Formula FormulaBuilder::negation(const Formula& f)
{
  CALL("FormulaBuilder::negation");

  if(!f.isValid()) {
    throw ApiException("Attempting to negate a formula created prior to a hard solver reset");
  }

  Formula res(new Kernel::NegatedFormula(f.form));
  res._aux=_aux; //assign the correct helper object
  return res;
}

Formula FormulaBuilder::formula(Connective c,const Formula& f1,const Formula& f2)
{
  CALL("FormulaBuilder::formula(Connective,const Formula&,const Formula&)");

  if(!f1.isValid() || !f2.isValid()) {
    throw ApiException("Attempting to create a complex formula from formulas created prior to a hard solver reset");
  }

  Kernel::Connective con;

  switch(c) {
  case AND:
    con=Kernel::AND;
    break;
  case OR:
    con=Kernel::OR;
    break;
  case IMP:
    con=Kernel::IMP;
    break;
  case IFF:
    con=Kernel::IFF;
    break;
  case XOR:
    con=Kernel::XOR;
    break;
  default:
    throw FormulaBuilderException("Invalid binary connective");
  }

  Formula res;
  switch(c) {
  case AND:
  case OR:
  {
    Kernel::FormulaList* flst=0;
    Kernel::FormulaList::push(f2.form, flst);
    Kernel::FormulaList::push(f1.form, flst);
    res=Formula(new Kernel::JunctionFormula(con, flst));
    break;
  }
  case IMP:
  case IFF:
  case XOR:
    res=Formula(new Kernel::BinaryFormula(con, f1.form, f2.form));
    break;
  default:
    ASSERTION_VIOLATION;
  }
  ASS(res.form);
  res._aux=_aux; //assign the correct helper object
  return res;
}

Formula FormulaBuilder::formula(Connective q,const Var& v,const Formula& f)
{
  CALL("FormulaBuilder::formula(Connective,const Var&,const Formula&)");

  if(!f.isValid()) {
    throw ApiException("Attempting to quantify a formula created prior to a hard solver reset");
  }
  if(_aux->_checkBindingBoundVariables) {
    VarList* boundVars=static_cast<Kernel::Formula*>(f)->boundVariables();
    bool alreadyBound=VarList::member(v, boundVars);
    VarList::destroy(boundVars);
    if(alreadyBound) {
      throw FormulaBuilderException("Attempt to bind a variable that is already bound: "+_aux->getVarName(v));
    }
  }

  Kernel::Connective con;

  switch(q) {
  case FORALL:
    con=Kernel::FORALL;
    break;
  case EXISTS:
    con=Kernel::EXISTS;
    break;
  default:
    throw FormulaBuilderException("Invalid quantifier connective");
  }

  Kernel::Formula::VarList* varList=0;
  Kernel::Formula::VarList::push(v, varList);

  //for now we are taking the easy method of not specifying a sort
  //However, we should change this so that the sort is added as well
  //AYB
  Formula res(new QuantifiedFormula(con, varList, 0, f.form));
  res._aux=_aux; //assign the correct helper object
  return res;
}

AnnotatedFormula FormulaBuilder::annotatedFormula(Formula f, Annotation a, vstring name)
{
  CALL("FormulaBuilder::annotatedFormula");

  if(!f.isValid()) {
    throw FormulaBuilderException("Attempting to annontate a formula created prior to a hard solver reset");
  }

  Kernel::UnitInputType inputType;
  bool negate=false;
  switch(a) {
  case AXIOM:
    inputType=Kernel::UnitInputType::AXIOM;
    break;
  case ASSUMPTION:
    inputType=Kernel::UnitInputType::ASSUMPTION;
    break;
  case CONJECTURE:
    inputType=Kernel::UnitInputType::CONJECTURE;
    negate=true;
    break;
  }

  if(negate) {
    Formula inner(Kernel::Formula::quantify(f));
    inner._aux=_aux;
    f=negation(inner);
  }

  FormulaUnit* fures=new Kernel::FormulaUnit(f, FromInput(inputType));

  AnnotatedFormula res(fures);
  res._aux=_aux; //assign the correct helper object

  if(name!="") {
    AnnotatedFormula::assignName(res, name);
  }

  return res;
}


Term FormulaBuilder::substitute(Term original, Var v, Term t)
{
  CALL("FormulaBuilder::substitute(Term)");

  Kernel::TermList tgt = static_cast<Kernel::TermList>(t);
  SingleVarApplicator apl(v, tgt);
  Kernel::TermList resTerm = SubstHelper::apply(static_cast<Kernel::TermList>(original), apl);
  return Term(resTerm, _aux);
}

Formula FormulaBuilder::substitute(Formula f, Var v, Term t)
{
  CALL("FormulaBuilder::substitute(Formula)");

  Kernel::Formula::VarList* fBound = f.form->boundVariables();
  if(Kernel::Formula::VarList::member(v, fBound)) {
    throw ApiException("Variable we substitute for cannot be bound in the formula");
  }

  Kernel::TermList trm = static_cast<Kernel::TermList>(t);
  Kernel::VariableIterator vit(trm);
  while(vit.hasNext()) {
    Kernel::TermList tVar = vit.next();
    ASS(tVar.isOrdinaryVar());
    if(Kernel::Formula::VarList::member(tVar.var(), fBound)) {
      throw ApiException("Variable in the substituted term cannot be bound in the formula");
    }
  }

  SingleVarApplicator apl(v, trm);
  Kernel::Formula* resForm = SubstHelper::apply(f.form, apl);
  return Formula(resForm, _aux);
}

AnnotatedFormula FormulaBuilder::substitute(AnnotatedFormula af, Var v, Term t)
{
  CALL("FormulaBuilder::substitute(AnnotatedFormula)");

  Formula substForm = substitute(af.formula(), v, t);
  return annotatedFormula(substForm, af.annotation());
}

Term FormulaBuilder::replaceConstant(Term original, Term replaced, Term target)
{
  CALL("FormulaBuilder::replaceConstant(Term)");

  Kernel::TermList trm = static_cast<Kernel::TermList>(original);
  Kernel::TermList tSrc = static_cast<Kernel::TermList>(replaced);
  Kernel::TermList tTgt = static_cast<Kernel::TermList>(target);

  if(!tSrc.isTerm() || tSrc.term()->arity()!=0) {
    throw ApiException("The replaced term must be a constant (zero-arity function)");
  }

  if(!trm.containsSubterm(replaced)) {
    return original;
  }
  //We only have function that replaces subterm in a literal. So we wrap the
  //term inside a literal, transform it and the unwrap it
  unsigned unaryPred = _aux->getUnaryPredicate();
  Kernel::Literal* aux = Literal::create1(unaryPred, true, original);
  Kernel::Literal* auxRepl = EqHelper::replace(aux, tSrc, tTgt);
  Kernel::TermList res = *auxRepl->nthArgument(0);
  return Term(res, _aux);
}

/*Formula FormulaBuilder::replaceConstant(Formula f, Term replaced, Term target)
{
  CALL("FormulaBuilder::replaceConstant(Formula)");

  Kernel::TermList tSrc = static_cast<Kernel::TermList>(replaced);
  Kernel::TermList tTgt = static_cast<Kernel::TermList>(target);

  if(!tSrc.isTerm() || tSrc.term()->arity()!=0) {
    throw ApiException("The replaced term must be a constant (zero-arity function)");
  }

  Kernel::Formula::VarList* fBound = f.form->boundVariables();
  VariableIterator vit(tTgt);
  while(vit.hasNext()) {
    Kernel::TermList tVar = vit.next();
    ASS(tVar.isOrdinaryVar());
    if(Kernel::Formula::VarList::member(tVar.var(), fBound)) {
      throw ApiException("Variable in the substituted term cannot be bound in the formula");
    }
  }

  Kernel::Formula* letForm = Formula::createLet(replaced.functor(), 0, target, f.form);
  Shell::FOOLElimination fe;
  FormulaUnit* auxUnit = new FormulaUnit(letForm, new Inference0(Inference::INPUT), Unit::AXIOM);
  UnitList* defs = 0;
  FormulaUnit* auxReplaced = fe.apply(auxUnit, defs);
  ASS_EQ(defs, 0);
  return Formula(auxReplaced->formula(), _aux);
}*/

/*AnnotatedFormula FormulaBuilder::replaceConstant(AnnotatedFormula af, Term replaced, Term target)
{
  CALL("FormulaBuilder::replaceConstant(AnnotatedFormula)");

  Formula replForm = replaceConstant(af.formula(), replaced, target);
  return annotatedFormula(replForm, af.annotation());
}*/


//////////////////////////////
// Convenience functions

void FormulaBuilder::checkForSortError(const Term& t1, const Term& t2)
{
  CALL("FormulaBuilder::checkForSortError")

  if(t1.sort() != t2.sort()){
    throw ApiException("Attempting to apply an arithmetic operation on terms of different sorts");
  }
  if(t1.sort() != integerSort() && t1.sort() != realSort() && t1.sort() != rationalSort()){
    throw ApiException("Attempting to apply an arithmetic operation on terms which are not of integer, real or rational sort");          
  }
}

Term FormulaBuilder::term(const Function& c)
{
  CALL("FormulaBuilder::term/0");

  return _aux->term(c,0,0);
}

Term FormulaBuilder::term(const Function& f,const Term& t)
{
  CALL("FormulaBuilder::term/1");

  return _aux->term(f,&t,1);
}

Term FormulaBuilder::term(const Function& f,const Term& t1,const Term& t2)
{
  CALL("FormulaBuilder::term/2");

  Term args[]={t1, t2};
  return _aux->term(f,args,2);
}

Term FormulaBuilder::term(const Function& f,const Term& t1,const Term& t2,const Term& t3)
{
  CALL("FormulaBuilder::term/3");

  Term args[]={t1, t2, t3};
  return _aux->term(f,args,3);
}

Term FormulaBuilder::integerConstantTerm(int i)
{
  CALL("FormulaBuilder::integerConstantTerm");

  return term(integerConstant(i));
}

Term FormulaBuilder::integerConstantTerm(Lib::vstring i)
{
  CALL("FormulaBuilder::integerConstantTerm");

  return term(integerConstant(i));
}


Term FormulaBuilder::rationalConstant(Lib::vstring numerator, Lib::vstring denom)
{
  CALL("FormulaBuilder::rationalConstant");

  return term(rationalConstantSymbol(numerator, denom));
}

Term FormulaBuilder::realConstant(Lib::vstring i)
{
  CALL("Solver::realConstant");

  return term(realConstantSymbol(i));
}

Term FormulaBuilder::sum(const Term& t1,const Term& t2)
{
  CALL("FormulaBuilder::sum");

  checkForSortError(t1, t2);
  
  Function sum;
  if(t1.sort() == integerSort()){
    sum = interpretedFunction(Kernel::Theory::INT_PLUS);
  } else if(t1.sort() == realSort()){
    sum = interpretedFunction(Kernel::Theory::REAL_PLUS);
  } else {
    sum = interpretedFunction(Kernel::Theory::RAT_PLUS);
  } 
  return term(sum, t1, t2);
}


Term FormulaBuilder::difference(const Term& t1,const Term& t2)
{
  CALL("FormulaBuilder::difference");

  checkForSortError(t1, t2);
  
  Function minus;
  if(t1.sort() == integerSort()){
    minus = interpretedFunction(Kernel::Theory::INT_MINUS);
  } else if(t1.sort() == realSort()){
    minus = interpretedFunction(Kernel::Theory::REAL_MINUS);
  } else {
    minus = interpretedFunction(Kernel::Theory::RAT_MINUS);
  } 
  return term(minus, t1, t2);
}

Term FormulaBuilder::multiply(const Term& t1,const Term& t2)
{
  CALL("FormulaBuilder::multiply");

  checkForSortError(t1, t2);
  
  Function mult;
  if(t1.sort() == integerSort()){
    mult = interpretedFunction(Kernel::Theory::INT_MULTIPLY);
  } else if(t1.sort() == realSort()){
    mult = interpretedFunction(Kernel::Theory::REAL_MULTIPLY);
  } else {
    mult = interpretedFunction(Kernel::Theory::RAT_MULTIPLY);
  } 
  return term(mult, t1, t2);
}

/* TODO what do we want here?
Term FormulaBuilder::divide(const Term& t1,const Term& t2)
{
  CALL("FormulaBuilder::divide");

  checkForSortError(t1, t2);
  
}*/

Term FormulaBuilder::floor(const Term& t1)
{
  CALL("FormulaBuilder::floor");

  if(t1.sort() != integerSort() && t1.sort() != realSort() && t1.sort() != rationalSort()){
    throw ApiException("Attempting to floor a term which is not of integer, real or rational sort");          
  }

  Function floor;
  if(t1.sort() == integerSort()){
    floor = interpretedFunction(Kernel::Theory::INT_FLOOR);
  } else if(t1.sort() == realSort()){
    floor = interpretedFunction(Kernel::Theory::REAL_FLOOR);
  } else {
    floor = interpretedFunction(Kernel::Theory::RAT_FLOOR);
  } 
  return term(floor, t1);
}

Term FormulaBuilder::ceiling(const Term& t1)
{
  CALL("FormulaBuilder::ceiling");

  if(t1.sort() != integerSort() && t1.sort() != realSort() && t1.sort() != rationalSort()){
    throw ApiException("Attempting to create the ceiling of a term which is not of integer, real or rational sort");          
  }

  Function ceiling;
  if(t1.sort() == integerSort()){
    ceiling = interpretedFunction(Kernel::Theory::INT_CEILING);
  } else if(t1.sort() == realSort()){
    ceiling = interpretedFunction(Kernel::Theory::REAL_CEILING);
  } else {
    ceiling = interpretedFunction(Kernel::Theory::RAT_CEILING);
  } 
  return term(ceiling, t1);
}

Term FormulaBuilder::absolute(const Term& t1)
{
  CALL("FormulaBuilder::absolute");

  if(t1.sort() != integerSort()){
    throw ApiException("Attempting to creat the absolute of a term which is not of integer sort");          
  }

  Function abs = interpretedFunction(Kernel::Theory::INT_ABS);
  return term(abs, t1);
}

Formula FormulaBuilder::geq(const Term& t1, const Term& t2)
{
  CALL("FormulaBuilder::geq");

  checkForSortError(t1, t2);
  
  Predicate geq;
  if(t1.sort() == integerSort()){
    geq = interpretedPredicate(Kernel::Theory::INT_GREATER_EQUAL);
  } else if(t1.sort() == realSort()){
    geq = interpretedPredicate(Kernel::Theory::REAL_GREATER_EQUAL);
  } else {
    geq = interpretedPredicate(Kernel::Theory::RAT_GREATER_EQUAL);
  } 
  return formula(geq, t1, t2);
}

Formula FormulaBuilder::leq(const Term& t1, const Term& t2)
{
  CALL("FormulaBuilder::leq");

  checkForSortError(t1, t2);
  
  Predicate leq;
  if(t1.sort() == integerSort()){
    leq = interpretedPredicate(Kernel::Theory::INT_LESS_EQUAL);
  } else if(t1.sort() == realSort()){
    leq = interpretedPredicate(Kernel::Theory::REAL_LESS_EQUAL);
  } else {
    leq = interpretedPredicate(Kernel::Theory::RAT_LESS_EQUAL);
  } 
  return formula(leq, t1, t2);
}

Formula FormulaBuilder::gt(const Term& t1, const Term& t2)
{
  CALL("FormulaBuilder::gt");

  checkForSortError(t1, t2);
  
  Predicate gt;
  if(t1.sort() == integerSort()){
    gt = interpretedPredicate(Kernel::Theory::INT_GREATER);
  } else if(t1.sort() == realSort()){
    gt = interpretedPredicate(Kernel::Theory::REAL_GREATER);
  } else {
    gt = interpretedPredicate(Kernel::Theory::RAT_GREATER);
  } 
  return formula(gt, t1, t2);
}

Formula FormulaBuilder::lt(const Term& t1, const Term& t2)
{
  CALL("FormulaBuilder::lt");

  checkForSortError(t1, t2);
  
  Predicate lt;
  if(t1.sort() == integerSort()){
    lt = interpretedPredicate(Kernel::Theory::INT_LESS);
  } else if(t1.sort() == realSort()){
    lt = interpretedPredicate(Kernel::Theory::REAL_LESS);
  } else {
    lt = interpretedPredicate(Kernel::Theory::RAT_LESS);
  } 
  return formula(lt, t1, t2);
}

Formula FormulaBuilder::formula(const Predicate& p)
{
  CALL("FormulaBuilder::formula/0");

  return _aux->atom(p,true,0,0);
}

Formula FormulaBuilder::formula(const Predicate& p,const Term& t)
{
  CALL("FormulaBuilder::formula/1");

  return _aux->atom(p,true,&t,1);
}

Formula FormulaBuilder::formula(const Predicate& p,const Term& t1,const Term& t2)
{
  CALL("FormulaBuilder::formula/2");

  Term args[]={t1, t2};
  return _aux->atom(p,true,args,2);
}

Formula FormulaBuilder::formula(const Predicate& p,const Term& t1,const Term& t2,const Term& t3)
{
  CALL("FormulaBuilder::formula/3");

  Term args[]={t1, t2, t3};
  return _aux->atom(p,true,args,3);
}

//////////////////////////////
// Wrapper implementation

bool Sort::isValid() const
{ return _num!=UINT_MAX && 
        (_num < Sorts::FIRST_USER_SORT || _aux->isValid()); }

bool Predicate::isValid() const
{ return _aux->isValid(); }

bool Function::isValid() const
{ return _aux->isValid(); }

Term::Term(Kernel::TermList t)
{
  content=t.content();
}

Term::Term(Kernel::TermList t, ApiHelper aux) : _aux(aux)
{
  content=t.content();
}

vstring Term::toString() const
{
  CALL("Term::toString");

  if(isNull()) {
    throw ApiException("Term not initialized");
  }
  if(!isValid()){
    throw ApiException("Term created prior to hard solver reset and cannot be printed");    
  }
  return _aux->toString(static_cast<Kernel::TermList>(*this));
}

bool Term::isValid() const
{ return _aux->isValid(); }

bool Term::isVar() const
{
  CALL("Term::isVar");

  if(isNull()) {
    throw ApiException("Term not initialized");
  }
  return static_cast<Kernel::TermList>(*this).isVar();
}

Var Term::var() const
{
  CALL("Term::var");

  if(isNull()) {
    throw ApiException("Term not initialized");
  }
  if(!isVar()) {
    throw ApiException("Variable can be retrieved only for a variable term");
  }
  return static_cast<Kernel::TermList>(*this).var();
}

Function Term::functor() const
{
  CALL("Term::functor");

  if(isNull()) {
    throw ApiException("Term not initialized");
  }
  if(!isValid()){
    throw ApiException("Functor cannot be retrieved for a term created prior to a hard solver reset");    
  }
  if(isVar()) {
    throw ApiException("Functor cannot be retrieved for a variable term");
  }
  return Function(static_cast<Kernel::TermList>(*this).term()->functor());
}

unsigned Term::arity() const
{
  CALL("Term::arity");

  if(isNull()) {
    throw ApiException("Term not initialized");
  }
  if(!isValid()){
    throw ApiException("Arity cannot be retrieved for a term created prior to a hard solver reset");    
  }
  if(isVar()) {
    throw ApiException("Arity cannot be retrieved for a variable term");
  }
  return static_cast<Kernel::TermList>(*this).term()->arity();
}

Term Term::arg(unsigned i)
{
  CALL("Term::arg");

  if(isNull()) {
    throw ApiException("Term not initialized");
  }
  if(isVar()) {
    throw ApiException("Arguments cannot be retrieved for a variable term");
  }
  if(!isValid()){
    throw ApiException("Arguments cannot be retrieved for a term created prior to a hard solver reset");    
  }
  if(i>=arity()) {
    throw ApiException("Argument index out of bounds");
  }
  return Term(*static_cast<Kernel::TermList>(*this).term()->nthArgument(i), _aux);
}

Sort Term::sort() const
{
  CALL("Term::sort");

  if(!isValid()) {
    throw ApiException("Cannot retrieve the sort of a term created prior to a hard solver reset");
  }
  Sort res = static_cast<FBHelperCore*>(*_aux)->getSort(*this);
  if(!res.isValid()) {
    throw ApiException("Cannot determine sort of a term");
  }
  return res;
}

Term::operator Kernel::TermList() const
{
  return TermList(content);
}

vstring Formula::toString() const
{
  CALL("Formula::toString");

  if(!isValid()){
    throw ApiException("Formula created prior to hard solver reset and cannot be printed");    
  }
  return static_cast<Kernel::Formula*>(*this)->toString();
}

bool Formula::isValid() const
{ return _aux->isValid(); }

bool Formula::isTrue() const
{ return form->connective()==Kernel::TRUE; }

bool Formula::isFalse() const
{ return form->connective()==Kernel::FALSE; }

bool Formula::isNegation() const
{ return form->connective()==Kernel::NOT; }

FormulaBuilder::Connective Formula::connective() const
{
  CALL("Formula::connective");

  switch(form->connective()) {
  case Kernel::LITERAL:
    ASS(form->literal()->isPositive());
    return FormulaBuilder::ATOM;
  case Kernel::AND:
    return FormulaBuilder::AND;
  case Kernel::OR:
    return FormulaBuilder::OR;
  case Kernel::IMP:
    return FormulaBuilder::IMP;
  case Kernel::IFF:
    return FormulaBuilder::IFF;
  case Kernel::XOR:
    return FormulaBuilder::XOR;
  case Kernel::NOT:
    return FormulaBuilder::NOT;
  case Kernel::FORALL:
    return FormulaBuilder::FORALL;
  case Kernel::EXISTS:
    return FormulaBuilder::EXISTS;
  case Kernel::TRUE:
    return FormulaBuilder::TRUE;
  case Kernel::FALSE:
    return FormulaBuilder::FALSE;
  default:
    ASSERTION_VIOLATION;
  }
}

Predicate Formula::predicate() const
{
  CALL("Formula::predicate");

  if(!isValid()){
    throw ApiException("Predicate cannot be retrieved from a formula created prior to a hard solver reset");    
  }
  if(form->connective()!=Kernel::LITERAL) {
    throw ApiException("Predicate symbol can be retrieved only from atoms");
  }
  return Predicate(form->literal()->functor());
}

bool Formula::atomPolarity() const
{
  CALL("Formula::atomPolarity");

  if(!isValid()){
    throw ApiException("Polarity cannot be retrieved from a formula created prior to a hard solver reset");    
  }
  if(form->connective()!=Kernel::LITERAL) {
    throw ApiException("Polarity can be retrieved only from atoms");
  }
  return form->literal()->polarity();
}


unsigned Formula::argCnt() const
{
  CALL("Formula::argCnt");
  
  if(!isValid()){
    throw ApiException("Argument count cannot be retrieved from a formula created prior to a hard solver reset");    
  }
  
  switch(form->connective()) {
  case Kernel::LITERAL:
    return form->literal()->arity();
  case Kernel::AND:
  case Kernel::OR:
    ASS_EQ(FormulaList::length(form->args()), 2);
    return 2;
  case Kernel::IMP:
  case Kernel::IFF:
  case Kernel::XOR:
    return 2;
  case Kernel::NOT:
  case Kernel::FORALL:
  case Kernel::EXISTS:
    return 1;
  case Kernel::TRUE:
  case Kernel::FALSE:
    return 0;
  default:
    ASSERTION_VIOLATION;
  }
}

Formula Formula::formulaArg(unsigned i)
{
  CALL("Formula::formulaArg");

  if(!isValid()){
    throw ApiException("Arguments cannot be retrieved from a formula created prior to a hard solver reset");    
  }

  Kernel::Formula* res = 0;
  switch(form->connective()) {
  case Kernel::LITERAL:
    throw ApiException("Formula arguments cannot be obtained from atoms");
  case Kernel::AND:
  case Kernel::OR:
    res = FormulaList::nth(form->args(), i);
    break;
  case Kernel::IMP:
  case Kernel::IFF:
  case Kernel::XOR:
    if(i==0) {
      res = form->left();
    } else if(i==1) {
      res = form->right();
    }
    break;
  case Kernel::NOT:
    if(i==0) {
      res = form->uarg();
    }
    break;
  case Kernel::FORALL:
  case Kernel::EXISTS:
    if(i==0) {
      res = form->qarg();
    }
    break;
  case Kernel::TRUE:
  case Kernel::FALSE:
    break;
  default:
    ASSERTION_VIOLATION;
  }
  if(res==0) {
    throw ApiException("Argument index out of bounds");
  }
  return Formula(res, _aux);
}

Term Formula::termArg(unsigned i)
{
  CALL("Formula::termArg");

  if(!isValid()){
    throw ApiException("Arguments cannot be retrieved from a formula created prior to a hard solver reset");    
  }
  if(form->connective()!=Kernel::LITERAL) {
    throw ApiException("Term arguments can be obtained only from atoms");
  }
  if(form->literal()->arity()<=i) {
    throw ApiException("Argument index out of bounds");
  }
  return Term(*form->literal()->nthArgument(i), _aux);
}

StringIterator Formula::freeVars()
{
  CALL("Formula::freeVars");

  if(!isValid()){
    throw ApiException("Free variables cannot be retrieved from a formula created prior to a hard solver reset");    
  }
  if(!form) {
    return StringIterator(VirtualIterator<vstring>::getEmpty());
  }
  VarList* vars=form->freeVariables();
  return _aux->getVarNames(vars);
}

StringIterator Formula::boundVars()
{
  CALL("Formula::boundVars");

  if(!isValid()){
    throw ApiException("Bound variables cannot be retrieved from a formula created prior to a hard solver reset");    
  }
  if(!form) {
    return StringIterator(VirtualIterator<vstring>::getEmpty());
  }
  VarList* vars=form->boundVariables();
  return _aux->getVarNames(vars);
}

vstring AnnotatedFormula::toString() const
{
  CALL("AnnotatedFormula::toString");

  if(!isValid()){
    throw ApiException("Cannot print a formula created prior to a hard solver reset");    
  }
  return unit->toString();
}

vstring AnnotatedFormula::name() const
{
  CALL("AnnotatedFormula::toString");

  vstring unitName;
  if(!Parse::TPTP::findAxiomName(unit, unitName)) {
    unitName="u" + Int::toString(unit->number());
  }
  return unitName;
}

bool AnnotatedFormula::isValid() const
{ return _aux->isValid(); }

StringIterator AnnotatedFormula::freeVars()
{
  CALL("AnnotatedFormula::freeVars");

  if(!isValid()){
    throw ApiException("Free variables cannot be retrieved from a formula created prior to a hard solver reset");    
  }
  if(!unit) {
    return StringIterator(VirtualIterator<vstring>::getEmpty());
  }
  VarList* vl=0;
  if(unit->isClause()) {
    VarList::pushFromIterator(static_cast<Clause*>(unit)->getVariableIterator(), vl);
  }
  else {
    vl=static_cast<FormulaUnit*>(unit)->formula()->freeVariables();
  }
  return _aux->getVarNames(vl);
}

StringIterator AnnotatedFormula::boundVars()
{
  CALL("AnnotatedFormula::boundVars");

  if(!isValid()){
    throw ApiException("Bound variables cannot be retrieved from a formula created prior to a hard solver reset");    
  }
  if(!unit || unit->isClause()) {
    return StringIterator(VirtualIterator<vstring>::getEmpty());
  }
  VarList* vl=static_cast<FormulaUnit*>(unit)->formula()->boundVariables();
  return _aux->getVarNames(vl);
}

FormulaBuilder::Annotation AnnotatedFormula::annotation() const
{
  CALL("AnnotatedFormula::annotation");

  switch(unit->inputType()) {
  case Kernel::UnitInputType::AXIOM:
    return FormulaBuilder::AXIOM;
  case Kernel::UnitInputType::ASSUMPTION:
    return FormulaBuilder::ASSUMPTION;
  case Kernel::UnitInputType::CONJECTURE:
    return FormulaBuilder::CONJECTURE;
  default:
    ASSERTION_VIOLATION;
  }
}

Formula AnnotatedFormula::formula()
{
  CALL("AnnotatedFormula::formula");

  if(!isValid()){
    throw ApiException("Cannot retrieve a formula created prior to a hard solver reset");    
  }

  if(unit->isClause()) {
    throw ApiException("Cannot retrieve formula from clausified object");
  }

  Kernel::Formula* form = static_cast<FormulaUnit*>(unit)->formula();

  if(unit->inputType()!=Kernel::UnitInputType::CONJECTURE) {
    return Formula(form, _aux);
  }

  //if we have a conjecture, we need to return negated formula
  if(form->connective()==Kernel::NOT) {
    return Formula(form->uarg(), _aux);
  }

  Kernel::Formula* negated = new Kernel::NegatedFormula(Kernel::Formula::quantify(form));
  return Formula(negated, _aux);
}

void AnnotatedFormula::assignName(AnnotatedFormula& form, vstring name)
{
  CALL("AnnotatedFormula::assignName");

  if(!form.isValid()){
    throw ApiException("Cannot assign a name to a formula created prior to a hard solver reset");    
  }

  if(!OutputOptions::assignFormulaNames()) {
    return;
  }

  static DHSet<vstring> usedNames;

  if(!usedNames.insert(name)) {
    vstring name0 = name;
    unsigned idx = 0;
    do {
      idx++;
      name = name0 + "_" + Int::toString(idx);
    } while(!usedNames.insert(name));
  }

  Parse::TPTP::assignAxiomName(form.unit, name);
}

///////////////////////
// OutputOptions
//

bool OutputOptions::_sortedEquality = false;
bool OutputOptions::_tffFormulas = false;
bool OutputOptions::_assignFormulaNames = true;

void OutputOptions::setAssignFormulaNames(bool newVal)
{
  CALL("OutputOptions::setAssignFormulaNames");

  _assignFormulaNames = newVal;
  env.options->setOutputAxiomNames(newVal);
}


//////////////////////////////
// StringIterator implementation

StringIterator::StringIterator(const VirtualIterator<vstring>& vit)
{
  CALL("StringIterator::StringIterator");

  _impl=new VirtualIterator<vstring>(vit);
}

StringIterator::~StringIterator()
{
  CALL("StringIterator::~StringIterator");

  if(_impl) {
    delete _impl;
  }
}

StringIterator::StringIterator(const StringIterator& it)
{
  CALL("StringIterator::StringIterator(StringIterator&)");

  if(it._impl) {
    _impl=new VirtualIterator<vstring>(*it._impl);
  }
  else {
    _impl=0;
  }
}

StringIterator& StringIterator::operator=(const StringIterator& it)
{
  CALL("StringIterator::operator=");

  VirtualIterator<vstring>* oldImpl=_impl;

  if(it._impl) {
    _impl=new VirtualIterator<vstring>(*it._impl);
  }
  else {
    _impl=0;
  }

  if(oldImpl) {
    delete oldImpl;
  }

  return *this;
}

bool StringIterator::hasNext()
{
  CALL("StringIterator::hasNext");

  if(!_impl) {
    return false;
  }

  return _impl->hasNext();
}

vstring StringIterator::next()
{
  CALL("StringIterator::next");

  if(!hasNext()) {
    throw FormulaBuilderException("next() function called on a StringIterator object that contains no more elements");
  }
  ASS(_impl);
  return _impl->next();
}

} //namespace Api


//////////////////////////////
// Output implementation

std::ostream& operator<< (std::ostream& str,const Api::Sort& sort)
{
  CALL("operator<< (ostream&,const Api::Sort&)");
  return str<<env.sorts->sortName(sort);
}

ostream& operator<< (ostream& str,const Api::Formula& f)
{
  CALL("operator<< (ostream&,const Api::Formula&)");
  return str<<f.toString();
}

ostream& operator<< (ostream& str,const Api::AnnotatedFormula& af)
{
  CALL("operator<< (ostream&,const Api::AnnotatedFormula&)");
  return str<<af.toString();
}

