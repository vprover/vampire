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

Sort FormulaBuilder::boolSort()
{
  CALL("FormulaBuilder::integerSort");

  return Sort(Sorts::SRT_BOOL);
}

Sort FormulaBuilder::defaultSort()
{
  CALL("FormulaBuilder::defaultSort");

  return Sort(Sorts::SRT_DEFAULT);
}

vstring FormulaBuilder::getSortName(Sort s)
{
  CALL("FormulaBuilder::getSortName");
  
  checkForValidity({s});
  return env.sorts->sortName(s);
}

vstring FormulaBuilder::getSymbolName(Symbol s)
{
  CALL("FormulaBuilder::getSymbolName");

  checkForValidity({s});
  return _aux->getSymbolName(!s.isFunctionSymbol(), s);
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

Symbol FormulaBuilder::symbol(const vstring& name, unsigned arity, Sort rangeSort, std::vector<Sort>& domainSorts, bool builtIn)
{
  CALL("FormulaBuilder::function/4");

  bool pred = (rangeSort == FormulaBuilder::boolSort());

  bool added;
  unsigned res = pred ? env.signature->addPredicate(name, arity, added):
                        env.signature->addFunction(name, arity, added);
  Kernel::Signature::Symbol* sym = pred ? env.signature->getPredicate(res):
                                          env.signature->getFunction(res);

  static DArray<unsigned> nativeSorts;
  nativeSorts.initFromArray(arity, domainSorts.data());

  OperatorType* type = pred ?
                       OperatorType::getPredicateType(arity, nativeSorts.array()):
                       OperatorType::getFunctionType(arity, nativeSorts.array(), rangeSort);

  if(added) {
    sym->setType(type);
  }
  else {
    if(type != (pred ? sym->predType() : sym->fnType())) {
      throw FormulaBuilderException("Creating symbol " + sym->name() + " with different type than a previously created function "
	  "of the same name and arity. (This must not happen even across different instances of the FormulaBuilder class.)");
    }
  }
  if(builtIn) {
    sym->markProtected();
  }
  return Symbol(res, pred, _aux);
}

Symbol FormulaBuilder::integerConstant(int i)
{
  CALL("FormulaBuilder::integerConstant");

  unsigned fun = env.signature->addIntegerConstant(IntegerConstantType(i));
  return Symbol(fun, false, _aux);
}

Symbol FormulaBuilder::integerConstant(vstring i)
{
  CALL("FormulaBuilder::integerConstant");

  unsigned fun;
  try {
    fun = env.signature->addIntegerConstant(IntegerConstantType(i));
  }
  catch (ArithmeticException) {
    throw FormulaBuilderException("Constant value invalid or does not fit into internal representation: " + i);
  }
  return Symbol(fun, false, _aux);
}

Symbol FormulaBuilder::rationalConstantSymbol(Lib::vstring numerator, Lib::vstring denom)
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
  return Symbol(fun, false, _aux);
}

Symbol FormulaBuilder::realConstantSymbol(Lib::vstring r)
{
  CALL("FormulaBuilder::realConstantSymbol");

  unsigned fun;
  try {
    fun = env.signature->addRealConstant(RealConstantType(r));
  }
  catch (ArithmeticException) {
    throw FormulaBuilderException("An arithmetic exception occured during the creation of constant " + r);
  }
  return Symbol(fun, false, _aux);
}

bool FormulaBuilder::checkNames(){
  CALL("FormulaBuilder::checkNames");
  
  return _aux->_checkNames;
}

void FormulaBuilder::reset(){
  CALL("FormulaBuilder::reset");

  _aux.resetCore();
}

Symbol FormulaBuilder::interpretedSymbol(Kernel::Theory::Interpretation interp)
{
  CALL("FormulaBuilder::interpretedPredicate");

  unsigned res = env.signature->getInterpretingSymbol(interp);
  return Symbol(res, !Theory::isFunction(interp), _aux);
}

/*
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
*/

Expression FormulaBuilder::varTerm(const Var& v)
{
  CALL("FormulaBuilder::varTerm");

  Expression res(Kernel::TermList(v,false));
  res._aux=_aux; //assign the correct helper object
  return res;
}

Expression FormulaBuilder::term(const Symbol& s,const std::vector<Expression>& args)
{
  CALL("FormulaBuilder::term");

  unsigned arity = s.isFunctionSymbol() ? env.signature->functionArity(s) : env.signature->predicateArity(s);
  return _aux->term(s,args.data(), arity);
}

Expression FormulaBuilder::equality(const Expression& lhs,const Expression& rhs, Sort sort, bool positive)
{
  CALL("FormulaBuilder::equality/4");

  if(lhs.sort()!=sort) {
    throw SortMismatchException("Sorts of equality sides is not as declared");
  }
  return equality(lhs, rhs, positive);
}

Expression FormulaBuilder::equality(const Expression& lhs,const Expression& rhs, bool positive)
{
  CALL("FormulaBuilder::equality/3");

  checkForValidity({lhs, rhs});
  if(!lhs.isTerm() || !rhs.isTerm()){
    throw ApiException("Formulas cannot occur on the left or right of an equality!");     
  }

  _aux->ensureEqualityArgumentsSortsMatch(lhs, rhs);
  unsigned srt = lhs.sort();
  if(srt!=rhs.sort()) {
    throw FormulaBuilderException("sort mismatch in equality creation: "+lhs.toString()+" = "+rhs.toString());
  }
  Literal* lit = Kernel::Literal::createEquality(positive, lhs, rhs, srt);
  return Expression(new Kernel::AtomicFormula(lit), _aux);
}

Expression FormulaBuilder::trueFormula()
{
  CALL("FormulaBuilder::trueFormula");

  return Expression(new Kernel::Formula(true), _aux);
}

Expression FormulaBuilder::falseFormula()
{
  CALL("FormulaBuilder::falseFormula");

  return Expression(new Kernel::Formula(false), _aux);
}

Expression FormulaBuilder::negation(const Expression& f)
{
  CALL("FormulaBuilder::negation");

  checkForValidity({f});
  checkForTermError({f});
  return Expression(new Kernel::NegatedFormula(f._form), _aux);
}

Expression FormulaBuilder::andFormula(const Expression& f1,const Expression& f2)
{
  CALL("FormulaBuilder::andFormula");

  return andOrOrFormula(Kernel::AND, f1, f2);
}

Expression FormulaBuilder::orFormula(const Expression& f1,const Expression& f2)
{
  CALL("FormulaBuilder::andFormula");

  return andOrOrFormula(Kernel::OR, f1, f2);
}

Expression FormulaBuilder::andOrOrFormula(Kernel::Connective c, const Expression& f1,const Expression& f2)
{
  CALL("FormulaBuilder::andOrOrFormula");

  checkForValidity({f1, f2});
  checkForTermError({f1, f2});

  Kernel::FormulaList* flst=0;
  Kernel::FormulaList::push(f2._form, flst);
  Kernel::FormulaList::push(f1._form, flst);
  return Expression(new Kernel::JunctionFormula(c, flst), _aux);  
}

Expression FormulaBuilder::implies(const Expression& f1,const Expression& f2)
{
  CALL("FormulaBuilder::implies");

  checkForValidity({f1, f2});
  checkForTermError({f1, f2});
  return Expression(new Kernel::BinaryFormula(Kernel::IMP, f1._form, f2._form), _aux);
}

Expression FormulaBuilder::iff(const Expression& f1,const Expression& f2)
{
  CALL("FormulaBuilder::iff");

  checkForValidity({f1, f2});
  checkForTermError({f1, f2});
  return Expression(new Kernel::BinaryFormula(Kernel::IFF, f1._form, f2._form), _aux);
}

Expression FormulaBuilder::exor(const Expression& f1,const Expression& f2)
{
  CALL("FormulaBuilder::exor");

  checkForValidity({f1, f2});
  checkForTermError({f1, f2});
  return Expression(new Kernel::BinaryFormula(Kernel::XOR, f1._form, f2._form), _aux);
}

Expression FormulaBuilder::exists(const Var& v,const Expression& f)
{
  CALL("FormulaBuilder::exists");

  return quantifiedFormula(Kernel::EXISTS, v, f);
}

Expression FormulaBuilder::forall(const Var& v,const Expression& f)
{
  CALL("FormulaBuilder::forall");

  return quantifiedFormula(Kernel::FORALL, v, f);
}

Expression FormulaBuilder::quantifiedFormula(Kernel::Connective con,const Var& v,const Expression& f)
{
  CALL("FormulaBuilder::quantifiedFormula");

  checkForValidity({f});
  checkForTermError({f});
  if(_aux->_checkBindingBoundVariables) {
    VarList* boundVars=static_cast<Kernel::Formula*>(f)->boundVariables();
    bool alreadyBound=VarList::member(v, boundVars);
    VarList::destroy(boundVars);
    if(alreadyBound) {
      throw FormulaBuilderException("Attempt to bind a variable that is already bound: "+_aux->getVarName(v));
    }
  }

  Kernel::Formula::VarList* varList=0;
  Kernel::Formula::VarList::push(v, varList);

  return Expression(new QuantifiedFormula(con, varList, 0, f._form), _aux);
}

AnnotatedFormula FormulaBuilder::annotatedFormula(Expression& f, Annotation a, vstring name)
{
  CALL("FormulaBuilder::annotatedFormula");

  ASS(!f.isTerm());

  if(!f.isValid()) {
    throw FormulaBuilderException("Attempting to add formula / conjecture created prior to a hard solver reset");
  }
  if(f.isTerm()){
    throw ApiException("Cannot assert expression " + f.toString() + " as it is not of Boolean sort");      
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
    Expression inner(Kernel::Formula::quantify(f), _aux);
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

Expression FormulaBuilder::substitute(Expression original, Var v, Expression t)
{
  CALL("FormulaBuilder::substitute(Formula)");

  ASS(!t.isTerm())

  Kernel::TermList trm = static_cast<Kernel::TermList>(t);
  if(original.isTerm()){
    SingleVarApplicator apl(v, trm);
    Kernel::TermList resTerm = SubstHelper::apply(static_cast<Kernel::TermList>(original), apl);
    return Expression(resTerm, _aux);
  }

  Kernel::Formula::VarList* fBound = original._form->boundVariables();
  if(Kernel::Formula::VarList::member(v, fBound)) {
    throw ApiException("Variable we substitute for cannot be bound in the formula");
  }

  Kernel::VariableIterator vit(trm);
  while(vit.hasNext()) {
    Kernel::TermList tVar = vit.next();
    ASS(tVar.isOrdinaryVar());
    if(Kernel::Formula::VarList::member(tVar.var(), fBound)) {
      throw ApiException("Variable in the substituted term cannot be bound in the formula");
    }
  }

  SingleVarApplicator apl(v, trm);
  Kernel::Formula* resForm = SubstHelper::apply(original._form, apl);
  return Expression(resForm, _aux);
}

AnnotatedFormula FormulaBuilder::substitute(AnnotatedFormula af, Var v, Expression t)
{
  CALL("FormulaBuilder::substitute(AnnotatedFormula)");

  Expression substForm = substitute(af.formula(), v, t);
  return annotatedFormula(substForm, af.annotation());
}

Expression FormulaBuilder::replaceConstant(Expression original, Expression replaced, Expression target)
{
  CALL("FormulaBuilder::replaceConstant(Term)");

  if(!original.isTerm() || !replaced.isTerm() || !target.isTerm()) {
    throw ApiException("Formulas cannot be used in replaceConstant function");
  }

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
  return Expression(res, _aux);
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

void FormulaBuilder::checkForNumericalSortError(std::initializer_list<Expression> exprs)
{
  CALL("FormulaBuilder::checkForNumericalSortError");
 
  Sort sort = std::begin(exprs)->sort();
  for( auto e : exprs )
  {
    if(e.sort() != sort){
      throw ApiException("Attempting to apply an arithmetic operation on terms of different sorts");
    }
    if(e.sort() != integerSort() && e.sort() != realSort() && e.sort() != rationalSort()){
      throw ApiException("Attempting to apply an arithmetic operation on expression " 
                          + e.toString() + " which is not of integer, real or rational sort");          
    }  
  }  
}

void FormulaBuilder::checkForTermError(std::initializer_list<Expression> exprs)
{
  CALL("FormulaBuilder::checkForBooleanSortError");

  for( auto e : exprs )
  {
    if(e.isTerm()){
      throw ApiException("Attempting to buila a formula using expresion " 
                          + e.toString() + " which is not of Boolean sort");          
    }  
  }    
}

template<class T>
void FormulaBuilder::checkForValidity(std::initializer_list<T> list)
{
  CALL("FormulaBuilder::checkForValidity");

  for( auto item : list )
  {
    if(!item.isValid()){
      throw ApiException("Attempting to use a Sort, Symbol or Expression created prior to a hard solver reset");          
    }  
  }   

}

Expression FormulaBuilder::term(const Symbol& s)
{
  CALL("FormulaBuilder::term/0");

  return _aux->term(s,0,0);
}

Expression FormulaBuilder::term(const Symbol& s,const Expression& t)
{
  CALL("FormulaBuilder::term/1");

  return _aux->term(s,&t,1);
}

Expression FormulaBuilder::term(const Symbol& s,const Expression& t1,const Expression& t2)
{
  CALL("FormulaBuilder::term/2");

  Expression args[]={t1, t2};
  return _aux->term(s,args,2);
}

Expression FormulaBuilder::term(const Symbol& s,const Expression& t1,const Expression& t2,const Expression& t3)
{
  CALL("FormulaBuilder::term/3");

  Expression args[]={t1, t2, t3};
  return _aux->term(s,args,3);
}

Expression FormulaBuilder::integerConstantTerm(int i)
{
  CALL("FormulaBuilder::integerConstantTerm");

  return term(integerConstant(i));
}

Expression FormulaBuilder::integerConstantTerm(Lib::vstring i)
{
  CALL("FormulaBuilder::integerConstantTerm");

  return term(integerConstant(i));
}


Expression FormulaBuilder::rationalConstant(Lib::vstring numerator, Lib::vstring denom)
{
  CALL("FormulaBuilder::rationalConstant");

  return term(rationalConstantSymbol(numerator, denom));
}

Expression FormulaBuilder::realConstant(Lib::vstring i)
{
  CALL("Solver::realConstant");

  return term(realConstantSymbol(i));
}

Expression FormulaBuilder::sum(const Expression& t1,const Expression& t2)
{
  CALL("FormulaBuilder::sum");

  checkForNumericalSortError({t1, t2});
  
  Symbol sum;
  if(t1.sort() == integerSort()){
    sum = interpretedSymbol(Kernel::Theory::INT_PLUS);
  } else if(t1.sort() == realSort()){
    sum = interpretedSymbol(Kernel::Theory::REAL_PLUS);
  } else {
    sum = interpretedSymbol(Kernel::Theory::RAT_PLUS);
  } 
  return term(sum, t1, t2);
}


Expression FormulaBuilder::difference(const Expression& t1,const Expression& t2)
{
  CALL("FormulaBuilder::difference");

  checkForNumericalSortError({t1, t2});
  
  Symbol minus;
  if(t1.sort() == integerSort()){
    minus = interpretedSymbol(Kernel::Theory::INT_MINUS);
  } else if(t1.sort() == realSort()){
    minus = interpretedSymbol(Kernel::Theory::REAL_MINUS);
  } else {
    minus = interpretedSymbol(Kernel::Theory::RAT_MINUS);
  } 
  return term(minus, t1, t2);
}

Expression FormulaBuilder::multiply(const Expression& t1,const Expression& t2)
{
  CALL("FormulaBuilder::multiply");

  checkForNumericalSortError({t1, t2});
  
  Symbol mult;
  if(t1.sort() == integerSort()){
    mult = interpretedSymbol(Kernel::Theory::INT_MULTIPLY);
  } else if(t1.sort() == realSort()){
    mult = interpretedSymbol(Kernel::Theory::REAL_MULTIPLY);
  } else {
    mult = interpretedSymbol(Kernel::Theory::RAT_MULTIPLY);
  } 
  return term(mult, t1, t2);
}

/* TODO what do we want here?
Term FormulaBuilder::divide(const Term& t1,const Term& t2)
{
  CALL("FormulaBuilder::divide");

  checkForNumericalSortError(t1, t2);
  
}*/

Expression FormulaBuilder::floor(const Expression& t1)
{
  CALL("FormulaBuilder::floor");

  checkForNumericalSortError({t1});

  Symbol floor;
  if(t1.sort() == integerSort()){
    floor = interpretedSymbol(Kernel::Theory::INT_FLOOR);
  } else if(t1.sort() == realSort()){
    floor = interpretedSymbol(Kernel::Theory::REAL_FLOOR);
  } else {
    floor = interpretedSymbol(Kernel::Theory::RAT_FLOOR);
  } 
  return term(floor, t1);
}

Expression FormulaBuilder::ceiling(const Expression& t1)
{
  CALL("FormulaBuilder::ceiling");

  checkForNumericalSortError({t1});

  Symbol ceiling;
  if(t1.sort() == integerSort()){
    ceiling = interpretedSymbol(Kernel::Theory::INT_CEILING);
  } else if(t1.sort() == realSort()){
    ceiling = interpretedSymbol(Kernel::Theory::REAL_CEILING);
  } else {
    ceiling = interpretedSymbol(Kernel::Theory::RAT_CEILING);
  } 
  return term(ceiling, t1);
}

Expression FormulaBuilder::absolute(const Expression& t1)
{
  CALL("FormulaBuilder::absolute");

  if(t1.sort() != integerSort()){
    throw ApiException("Attempting to creat the absolute of a term which is not of integer sort");          
  }

  Symbol abs = interpretedSymbol(Kernel::Theory::INT_ABS);
  return term(abs, t1);
}

Expression FormulaBuilder::geq(const Expression& t1, const Expression& t2)
{
  CALL("FormulaBuilder::geq");

  checkForNumericalSortError({t1, t2});
  
  Symbol geq;
  if(t1.sort() == integerSort()){
    geq = interpretedSymbol(Kernel::Theory::INT_GREATER_EQUAL);
  } else if(t1.sort() == realSort()){
    geq = interpretedSymbol(Kernel::Theory::REAL_GREATER_EQUAL);
  } else {
    geq = interpretedSymbol(Kernel::Theory::RAT_GREATER_EQUAL);
  } 
  return term(geq, t1, t2);
}

Expression FormulaBuilder::leq(const Expression& t1, const Expression& t2)
{
  CALL("FormulaBuilder::leq");

  checkForNumericalSortError({t1, t2});
  
  Symbol leq;
  if(t1.sort() == integerSort()){
    leq = interpretedSymbol(Kernel::Theory::INT_LESS_EQUAL);
  } else if(t1.sort() == realSort()){
    leq = interpretedSymbol(Kernel::Theory::REAL_LESS_EQUAL);
  } else {
    leq = interpretedSymbol(Kernel::Theory::RAT_LESS_EQUAL);
  } 
  return term(leq, t1, t2);
}

Expression FormulaBuilder::gt(const Expression& t1, const Expression& t2)
{
  CALL("FormulaBuilder::gt");

  checkForNumericalSortError({t1, t2});
  
  Symbol gt;
  if(t1.sort() == integerSort()){
    gt = interpretedSymbol(Kernel::Theory::INT_GREATER);
  } else if(t1.sort() == realSort()){
    gt = interpretedSymbol(Kernel::Theory::REAL_GREATER);
  } else {
    gt = interpretedSymbol(Kernel::Theory::RAT_GREATER);
  } 
  return term(gt, t1, t2);
}

Expression FormulaBuilder::lt(const Expression& t1, const Expression& t2)
{
  CALL("FormulaBuilder::lt");

  checkForNumericalSortError({t1, t2});
  
  Symbol lt;
  if(t1.sort() == integerSort()){
    lt = interpretedSymbol(Kernel::Theory::INT_LESS);
  } else if(t1.sort() == realSort()){
    lt = interpretedSymbol(Kernel::Theory::REAL_LESS);
  } else {
    lt = interpretedSymbol(Kernel::Theory::RAT_LESS);
  } 
  return term(lt, t1, t2);
}

//////////////////////////////
// Wrapper implementation

bool Sort::isValid() const
{ return _num!=UINT_MAX && 
        (_num < Sorts::FIRST_USER_SORT || _aux->isValid()); }

bool Symbol::isValid() const
{ return _aux->isValid(); }


Expression::Expression(Kernel::TermList t) : _isTerm(1)
{
  _content=t.content();
}

Expression::Expression(Kernel::TermList t, ApiHelper aux) : _isTerm(1), _aux(aux)
{
  _content=t.content();
}

vstring Expression::toString() const
{
  CALL("Expression::toString");

  if(isNull()) {
    throw ApiException("Expression not initialized");
  }
  if(!isValid()){
    throw ApiException("Expression created prior to hard solver reset and cannot be printed");    
  }
  if(isTerm()){
    return _aux->toString(static_cast<Kernel::TermList>(*this));
  }
  return static_cast<Kernel::Formula*>(*this)->toString();
}

bool Expression::isValid() const
{ return _aux->isValid(); }

bool Expression::isVar() const
{
  CALL("Expression::isVar");

  if(isNull()) {
    throw ApiException("Expression not initialized");
  }
  if(!isTerm()){
    return false;
  }
  return static_cast<Kernel::TermList>(*this).isVar();
}

Var Expression::var() const
{
  CALL("Expression::var");

  if(!isVar()) {
    throw ApiException("Variable can be retrieved only for a variable term");
  }
  return static_cast<Kernel::TermList>(*this).var();
}

Symbol Expression::functor() const
{
  CALL("Expression::functor");

  if(isNull()) {
    throw ApiException("Expression not initialized");
  }
  if(!isValid()){
    throw ApiException("Functor cannot be retrieved for an expression created prior to a hard solver reset");    
  }
  if(isVar()) {
    throw ApiException("Functor cannot be retrieved for a variable expression");
  }
  if(isTerm()){
    return Symbol(static_cast<Kernel::TermList>(*this).term()->functor(), false, _aux);
  }
  return Symbol(_form->literal()->functor(), true, _aux);
}

unsigned Expression::arity() const
{
  CALL("Expression::arity");

  if(isNull()) {
    throw ApiException("Expression not initialized");
  }
  if(!isValid()){
    throw ApiException("Arity cannot be retrieved for an expression created prior to a hard solver reset");    
  }
  if(isVar()) {
    throw ApiException("Arity cannot be retrieved for a variable term");
  }
  if(isTerm()){
    return static_cast<Kernel::TermList>(*this).term()->arity();
  } else {
    switch(_form->connective()) {
      case Kernel::LITERAL:
        return _form->literal()->arity();
      case Kernel::AND:
      case Kernel::OR:
        ASS_EQ(FormulaList::length(_form->args()), 2);
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
}

Expression Expression::arg(unsigned i)
{
  CALL("Expression::arg");

  if(isNull()) {
    throw ApiException("Expression not initialized");
  }
  if(isVar()) {
    throw ApiException("Arguments cannot be retrieved for a variable term");
  }
  if(!isValid()){
    throw ApiException("Arguments cannot be retrieved for an expression created prior to a hard solver reset");    
  }
  if(i>=arity()) {
    throw ApiException("Argument index out of bounds");
  }
  if(isTerm()){
    return Expression(*static_cast<Kernel::TermList>(*this).term()->nthArgument(i), _aux);
  } else {
    return formulaArg(i);
  }
}

Sort Expression::sort() const
{
  CALL("Expression::sort");

  if(!isValid()) {
    throw ApiException("Cannot retrieve the sort of an expression created prior to a hard solver reset");
  }
  if(!isTerm()){
    return FormulaBuilder::boolSort();
  }
  Sort res = static_cast<FBHelperCore*>(*_aux)->getSort(*this);
  if(!res.isValid()) {
    throw ApiException("Cannot determine sort of a term");
  }
  return res;
}

Expression::operator Kernel::Formula*() const
{
  ASS(!isTerm());
  return _form;
}

Expression::operator Kernel::TermList() const
{  
  ASS(isTerm());
  return TermList(_content);
}

bool Expression::isTrue() const
{ 
  if(isTerm()){
    return false;
  }
  return _form->connective()==Kernel::TRUE; 
}

bool Expression::isFalse() const
{ 
  if(isTerm()){
    return false;    
  }
  return _form->connective()==Kernel::FALSE; 
}

bool Expression::isNegation() const
{ 
  if(isTerm()){
    return false;
  }
  return _form->connective()==Kernel::NOT; 
}

bool Expression::atomPolarity() const
{
  CALL("Expression::atomPolarity");

  if(!isValid()){
    throw ApiException("Polarity cannot be retrieved from an expression created prior to a hard solver reset");    
  }
  if(isTerm()){
    throw ApiException("Cannot retrieve the polarity of a non-formula");
  }
  if(_form->connective()!=Kernel::LITERAL) {
    throw ApiException("Polarity can be retrieved only from atoms");
  }
  return _form->literal()->polarity();
}

Expression Expression::formulaArg(unsigned i)
{
  CALL("Expression::formulaArg");

  Kernel::Formula* res = 0;
  switch(_form->connective()) {
  case Kernel::LITERAL:
    return Expression(*_form->literal()->nthArgument(i), _aux);
  case Kernel::AND:
  case Kernel::OR:
    res = FormulaList::nth(_form->args(), i);
    break;
  case Kernel::IMP:
  case Kernel::IFF:
  case Kernel::XOR:
    if(i==0) {
      res = _form->left();
    } else if(i==1) {
      res = _form->right();
    }
    break;
  case Kernel::NOT:
    if(i==0) {
      res = _form->uarg();
    }
    break;
  case Kernel::FORALL:
  case Kernel::EXISTS:
    if(i==0) {
      res = _form->qarg();
    }
    break;
  case Kernel::TRUE:
  case Kernel::FALSE:
    break;
  default:
    ASSERTION_VIOLATION;
  }
  ASS(res);//we do a check that i is within bounds in arity()
  return Expression(res, _aux);
}


StringIterator Expression::freeVars()
{
  CALL("Expression::freeVars");

  if(!isValid()){
    throw ApiException("Free variables cannot be retrieved from a formula created prior to a hard solver reset");    
  }
  //TODO it shouldn't be too dfficult to return free variables if we wanted to
  if(isTerm()){
    throw ApiException("Cannot retireve the free variables of a term");        
  }
  if(isNull()) {
    return StringIterator(VirtualIterator<vstring>::getEmpty());
  }
  VarList* vars=  _form->freeVariables();
  return _aux->getVarNames(vars);
}

StringIterator Expression::boundVars()
{
  CALL("Expression::boundVars");

  if(!isValid()){
    throw ApiException("Bound variables cannot be retrieved from a formula created prior to a hard solver reset");    
  }
  if(isNull() || isTerm()) {
    return StringIterator(VirtualIterator<vstring>::getEmpty());
  }
  VarList* vars=_form->boundVariables();
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

Expression AnnotatedFormula::formula()
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
    return Expression(form, _aux);
  }

  //if we have a conjecture, we need to return negated formula
  if(form->connective()==Kernel::NOT) {
    return Expression(form->uarg(), _aux);
  }

  Kernel::Formula* negated = new Kernel::NegatedFormula(Kernel::Formula::quantify(form));
  return Expression(negated, _aux);
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

ostream& operator<< (ostream& str,const Api::Expression& f)
{
  CALL("operator<< (ostream&,const Api::Expression&)");
  return str<<f.toString();
}

ostream& operator<< (ostream& str,const Api::AnnotatedFormula& af)
{
  CALL("operator<< (ostream&,const Api::AnnotatedFormula&)");
  return str<<af.toString();
}

