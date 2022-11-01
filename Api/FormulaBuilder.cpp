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
#include "Lib/VString.hpp"
#include "Lib/StringUtils.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubstHelper.hpp"
//#include "Kernel/Sorts.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Parse/TPTP.hpp"

#include "Shell/Options.hpp"
#include "Shell/FOOLElimination.hpp"
#include "Shell/TPTPPrinter.hpp"

using namespace std;
using namespace Lib;
using namespace Shell;

namespace Vampire
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

Sort FormulaBuilder::sort(const std::string& sortName)
{
  CALL("FormulaBuilder::sort");

  TermList res = TermList(AtomicSort::createConstant(StringUtils::copy2vstr(sortName)));
  Sort sort(res);
  sort._aux=_aux;
  return sort;
}

Sort FormulaBuilder::integerSort()
{
  CALL("FormulaBuilder::integerSort");

  return Sort(AtomicSort::intSort());
}

Sort FormulaBuilder::rationalSort()
{
  CALL("FormulaBuilder::integerSort");

  return Sort(AtomicSort::rationalSort());
}

Sort FormulaBuilder::realSort()
{
  CALL("FormulaBuilder::integerSort");

  return Sort(AtomicSort::realSort());
}

Sort FormulaBuilder::timeSort()
{
  CALL("FormulaBuilder::timeSort");

  return Sort(AtomicSort::timeSort());
}

Sort FormulaBuilder::boolSort()
{
  CALL("FormulaBuilder::integerSort");

  return Sort(AtomicSort::boolSort());
}

Sort FormulaBuilder::defaultSort()
{
  CALL("FormulaBuilder::defaultSort");

  return Sort(AtomicSort::defaultSort());
}

Sort FormulaBuilder::arraySort(const Sort& indexSort, const Sort& innerSort)
{
  CALL("FormulaBuilder::arraySort");

  TermList res = AtomicSort::arraySort(indexSort, innerSort);
  Sort sort(res);
  sort._aux=_aux;
  return sort;  
}

Field FormulaBuilder::field(std::string& fieldName, Sort fieldSort)
{
  CALL("FormulaBuilder::field");

  Field field(fieldName, fieldSort);
  field._aux=_aux;
  return field;
}

Field FormulaBuilder::field(std::string& fieldName, Sort fieldSort, std::string& chain,
  std::string& support)
{
  CALL("FormulaBuilder::field/2");

  Field field(fieldName, fieldSort, chain, support);
  field._aux=_aux;
  return field;
}

string FormulaBuilder::getSortName(Sort s)
{
  CALL("FormulaBuilder::getSortName");
  
  checkForValidity({s});
  return s.toString();
}

string FormulaBuilder::getSymbolName(Symbol s)
{
  CALL("FormulaBuilder::getSymbolName");

  checkForValidity({s});
  return StringUtils::copy2str(_aux->getSymbolName(!s.isFunctionSymbol(), s));
}

//TODO invalidate vars on a hard solver reset as well?
string FormulaBuilder::getVariableName(Var v)
{
  CALL("FormulaBuilder::getVariableName");

  return StringUtils::copy2str(_aux->getVarName(v));
}


Var FormulaBuilder::var(const string& varName)
{
  CALL("FormulaBuilder::var");

  if(!_aux->_allowImplicitlyTypedVariables) {
    throw FormulaBuilderException("Creating implicitly typed variables is not allowed. Use function "
	"FormulaBuilder::var(const vstring& varName, Sort varSort) instead of "
	"FormulaBuilder::var(const vstring& varName)");
  }

  return var(varName, defaultSort());
}

Var FormulaBuilder::var(const string& varName, Sort varSort)
{
  CALL("FormulaBuilder::var");

  vstring vVarName = StringUtils::copy2vstr(varName);
  return _aux->getVar(vVarName, varSort);
}

Symbol FormulaBuilder::symbol(const string& name, unsigned arity, Sort rangeSort, 
  std::vector<Sort>& domainSorts, RapidSym rs, bool builtIn)
{
  CALL("FormulaBuilder::symbol");
   
  bool pred = (rangeSort == FormulaBuilder::boolSort());

  vstring vname = StringUtils::copy2vstr(name);

  bool added;
  unsigned res = pred ? env.signature->addPredicate(vname, arity, added):
                        env.signature->addFunction(vname, arity, added);
  Kernel::Signature::Symbol* sym = pred ? env.signature->getPredicate(res):
                                          env.signature->getFunction(res);

  static DArray<TermList> nativeSorts;
  nativeSorts.initFromArray(arity, domainSorts.data());

  OperatorType* type = pred ?
                       OperatorType::getPredicateType(arity, nativeSorts.array()):
                       OperatorType::getFunctionType(arity, nativeSorts.array(), rangeSort);

  if(added) {
    sym->setType(type);
  }
  else {
    if(type != (pred ? sym->predType() : sym->fnType())) {
      throw FormulaBuilderException("Creating symbol " + StringUtils::copy2str(sym->name()) + " with different type than a previously created function "
	  "of the same name and arity. (This must not happen even across different instances of the FormulaBuilder class.)");
    }
  }
  if(rs == RapidSym::LEMMA_PRED){
    sym->markLemmaPred();
  }
  if(rs == RapidSym::MALLOC){
    sym->markMalloc();
  }
  if(rs == RapidSym::FN_LOOP_COUNT){
    sym->markFinalLoopCount();
  }
  if(rs == RapidSym::MAIN_END){
    sym->markMainEnd();
  }
  if(rs == RapidSym::TIME_POINT){
    sym->markTimePoint();
  }
  if(rs == RapidSym::CONST_VAR){
    sym->markConstantProgramVar();
  } 
  if(rs == RapidSym::PROGRAM_VAR){
    sym->markProgramVar();
  }   
  if(rs == RapidSym::CHAIN){
    sym->markChain();
  }
  if(rs == RapidSym::NULL_PTR){
    sym->markNullPtr();
  }  
  if(rs == RapidSym::OBJ_ARRAY){
    sym->markObjectArray();
  }
  if(rs == RapidSym::STRUCT_FIELD_SELF_POINTER){
    sym->markSelfPointer();
  }                
  if(builtIn) {
    sym->markProtected();
  }
  return Symbol(res, pred, _aux);
}

Symbol FormulaBuilder::integerConstant(int i)
{
  CALL("FormulaBuilder::integerConstant");

  return integerConstant(to_string(i));
}

Symbol FormulaBuilder::integerConstant(string i)
{
  CALL("FormulaBuilder::integerConstant");

  //no need to catch arithmetic exception as this is done in TPTP
  vstring num = StringUtils::copy2vstr(i);
  unsigned fun = Parse::TPTP::addIntegerConstant(num, _aux->getOverflow(), false);
  return Symbol(fun, false, _aux);
}

Symbol FormulaBuilder::rationalConstantSymbol(string r)
{
  CALL("FormulaBuilder::rationalConstantSymbol");

  Lib::vstring num = StringUtils::copy2vstr(r);
  unsigned fun = Parse::TPTP::addRationalConstant(num, _aux->getOverflow(), false);
  return Symbol(fun, false, _aux);
}

Symbol FormulaBuilder::realConstantSymbol(string r)
{
  CALL("FormulaBuilder::realConstantSymbol");


  Lib::vstring num = StringUtils::copy2vstr(r);
  unsigned fun = Parse::TPTP::addRealConstant(num, _aux->getOverflow(), false);
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

Symbol interpretedSymbol(Kernel::Theory::Interpretation interp, ApiHelper& aux)
{
  CALL("interpretedPredicate");

  unsigned res = env.signature->getInterpretingSymbol(interp);
  return Symbol(res, !Theory::isFunction(interp), aux);
}

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
  Kernel::TermList srt = lhs.sort();
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

  return andOrOrFormula(AND, {f1, f2});
}

Expression FormulaBuilder::andFormula(const std::vector<Expression>& conjuncts)
{
  CALL("FormulaBuilder::andFormula/2");

  return andOrOrFormula(AND, conjuncts);
}

Expression FormulaBuilder::orFormula(const Expression& f1,const Expression& f2)
{
  CALL("FormulaBuilder::orFormula");

  return andOrOrFormula(OR, {f1, f2});
}

Expression FormulaBuilder::orFormula(const std::vector<Expression>& disjuncts)
{
  CALL("FormulaBuilder::orFormula/2");

  return andOrOrFormula(OR, disjuncts);
}

Expression FormulaBuilder::andOrOrFormula(Connective con, const std::vector<Expression>& forms)
{
  CALL("FormulaBuilder::andOrOrFormula");

  for(auto f : forms)
  {
    if(!f.isValid()){
      throw ApiException("Attempting to use an Expression created prior to a hard solver reset");          
    }  
  }  

  if(forms.size() < 2){
    throw ApiException("AND and OR must have at least two operands");    
  }

  Kernel::FormulaList* flst=0;
  for(auto f : forms)
  {  
    Kernel::FormulaList::push(f._form, flst);
  }
  Kernel::Connective c = con == AND ? Kernel::AND : Kernel::OR;
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

  return quantifiedFormula(EXISTS, v, f);
}

Expression FormulaBuilder::forall(const Var& v,const Expression& f)
{
  CALL("FormulaBuilder::forall");

  return quantifiedFormula(FORALL, v, f);
}

Expression FormulaBuilder::quantifiedFormula(Connective con,const Var& v,const Expression& f)
{
  CALL("FormulaBuilder::quantifiedFormula");

  checkForValidity({f});
  checkForTermError({f});

  if(_aux->_checkBindingBoundVariables) {
    VList* boundVars=static_cast<Kernel::Formula*>(f)->boundVariables();
    bool alreadyBound=VList::member(v, boundVars);
    VList::destroy(boundVars);

    if(alreadyBound) {
      throw FormulaBuilderException("Attempt to bind a variable that is already bound: "+ StringUtils::copy2str(_aux->getVarName(v)));
    }
  }

  VList* varList=0;
  VList::push(v, varList);
  Kernel::Connective c = con == FORALL ? Kernel::FORALL : Kernel::EXISTS;

  return Expression(new QuantifiedFormula(c, varList, 0, f), _aux);
}

AnnotatedFormula FormulaBuilder::annotatedFormula(Expression& f, Annotation a, string name)
{
  CALL("FormulaBuilder::annotatedFormula");

  //TODO Allow the assertion of formula level ites
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

  VList* fBound = original._form->boundVariables();
  if(VList::member(v, fBound)) {
    throw ApiException("Variable we substitute for cannot be bound in the formula");
  }

  Kernel::VariableIterator vit(trm);
  while(vit.hasNext()) {
    Kernel::TermList tVar = vit.next();
    ASS(tVar.isOrdinaryVar());
    if(VList::member(tVar.var(), fBound)) {
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

  VList* fBound = f.form->boundVariables();
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
  CALL("FormulaBuilder::checkForTermError");

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

Expression FormulaBuilder::ite(const Expression& cond,const Expression& t1,const Expression& t2)
{
  CALL("FormulaBuilder::ite");

  checkForValidity<Expression>({cond, t1, t2});

  if(cond.sort() != boolSort()){
    throw ApiException("ITE error, cond " + cond.toString() + " is not of Boolean sort");
  }
  if(t1.sort() != t2.sort()){
    throw ApiException("ITE error, then expression " + t1.toString() + " has a different sort to else expression " + t2.toString());
  }
  
  return _aux->iteTerm(cond, t1, t2);
}

Expression FormulaBuilder::integerConstantTerm(int i)
{
  CALL("FormulaBuilder::integerConstantTerm");
  
  return term(integerConstant(i));
}

Expression FormulaBuilder::integerConstantTerm(string i)
{
  CALL("FormulaBuilder::integerConstantTerm");

  return term(integerConstant(i));
}

Expression FormulaBuilder::rationalConstant(string r)
{
  CALL("FormulaBuilder::rationalConstant");

  return term(rationalConstantSymbol(r));
}

Expression FormulaBuilder::realConstant(string i)
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
    sum = interpretedSymbol(Kernel::Theory::INT_PLUS, _aux);
  } else if(t1.sort() == realSort()){
    sum = interpretedSymbol(Kernel::Theory::REAL_PLUS, _aux);
  } else {
    sum = interpretedSymbol(Kernel::Theory::RAT_PLUS, _aux);
  } 
  return term(sum, t1, t2);
}


Expression FormulaBuilder::difference(const Expression& t1,const Expression& t2)
{
  CALL("FormulaBuilder::difference");

  checkForNumericalSortError({t1, t2});
  
  Symbol minus;
  if(t1.sort() == integerSort()){
    minus = interpretedSymbol(Kernel::Theory::INT_MINUS, _aux);
  } else if(t1.sort() == realSort()){
    minus = interpretedSymbol(Kernel::Theory::REAL_MINUS, _aux);
  } else {
    minus = interpretedSymbol(Kernel::Theory::RAT_MINUS, _aux);
  } 
  return term(minus, t1, t2);
}

Expression FormulaBuilder::multiply(const Expression& t1,const Expression& t2)
{
  CALL("FormulaBuilder::multiply");

  checkForNumericalSortError({t1, t2});
  
  Symbol mult;
  if(t1.sort() == integerSort()){
    mult = interpretedSymbol(Kernel::Theory::INT_MULTIPLY, _aux);
  } else if(t1.sort() == realSort()){
    mult = interpretedSymbol(Kernel::Theory::REAL_MULTIPLY, _aux);
  } else {
    mult = interpretedSymbol(Kernel::Theory::RAT_MULTIPLY, _aux);
  } 
  return term(mult, t1, t2);
}

Expression FormulaBuilder::div(const Expression& t1,const Expression& t2)
{
  CALL("FormulaBuilder::div");

  checkForNumericalSortError({t1, t2});
  
  Symbol div;
  if(t1.sort() == integerSort()){
    div = interpretedSymbol(Kernel::Theory::INT_REMAINDER_E, _aux);
  } else if(t1.sort() == realSort()){
    div = interpretedSymbol(Kernel::Theory::REAL_REMAINDER_E, _aux);
  } else {
    div = interpretedSymbol(Kernel::Theory::RAT_REMAINDER_E, _aux);
  } 
  return term(div, t1, t2);  
}

Expression FormulaBuilder::mod(const Expression& t1,const Expression& t2)
{
  CALL("FormulaBuilder::div");

  checkForNumericalSortError({t1, t2});

  Symbol mod;
  if(t1.sort() == integerSort()){
    mod = interpretedSymbol(Kernel::Theory::INT_QUOTIENT_E, _aux);
  } else if(t1.sort() == realSort()){
    mod = interpretedSymbol(Kernel::Theory::REAL_QUOTIENT_E, _aux);
  } else {
    mod = interpretedSymbol(Kernel::Theory::RAT_QUOTIENT_E, _aux);
  } 
  return term(mod, t1, t2);  
}

Expression FormulaBuilder::neg(const Expression& t)
{
  CALL("FormulaBuilder::div");

  checkForNumericalSortError({t});

  Symbol unaryMinus;
  if(t.sort() == integerSort()){
    unaryMinus = interpretedSymbol(Kernel::Theory::INT_UNARY_MINUS, _aux);
  } else if(t.sort() == realSort()){
    unaryMinus = interpretedSymbol(Kernel::Theory::REAL_UNARY_MINUS, _aux);
  } else {
    unaryMinus = interpretedSymbol(Kernel::Theory::RAT_UNARY_MINUS, _aux);
  } 
  return term(unaryMinus, t);  
}

Expression FormulaBuilder::int2real(const Expression& t)
{
  CALL("FormulaBuilder::int2real");
  
  if(t.sort() != integerSort()){
    throw ApiException("Cannot call int2real on " + t.toString() + " as it is not of integer sort");             
  }

  Symbol conv = interpretedSymbol(Kernel::Theory::INT_TO_REAL, _aux);
  return term(conv, t);
}

Expression FormulaBuilder::real2int(const Expression& t)
{
  CALL("FormulaBuilder::real2int");

  if(t.sort() != realSort()){
    throw ApiException("Cannot call int2real on " + t.toString() + " as it is not of real sort");             
  }

  Symbol conv = interpretedSymbol(Kernel::Theory::REAL_TO_INT, _aux);
  return term(conv, t);
}

Expression FormulaBuilder::floor(const Expression& t1)
{
  CALL("FormulaBuilder::floor");

  checkForNumericalSortError({t1});

  Symbol floor;
  if(t1.sort() == integerSort()){
    floor = interpretedSymbol(Kernel::Theory::INT_FLOOR, _aux);
  } else if(t1.sort() == realSort()){
    floor = interpretedSymbol(Kernel::Theory::REAL_FLOOR, _aux);
  } else {
    floor = interpretedSymbol(Kernel::Theory::RAT_FLOOR, _aux);
  } 
  return term(floor, t1);
}

Expression FormulaBuilder::ceiling(const Expression& t1)
{
  CALL("FormulaBuilder::ceiling");

  checkForNumericalSortError({t1});

  Symbol ceiling;
  if(t1.sort() == integerSort()){
    ceiling = interpretedSymbol(Kernel::Theory::INT_CEILING, _aux);
  } else if(t1.sort() == realSort()){
    ceiling = interpretedSymbol(Kernel::Theory::REAL_CEILING, _aux);
  } else {
    ceiling = interpretedSymbol(Kernel::Theory::RAT_CEILING, _aux);
  } 
  return term(ceiling, t1);
}

Expression FormulaBuilder::absolute(const Expression& t1)
{
  CALL("FormulaBuilder::absolute");

  if(t1.sort() != integerSort()){
    throw ApiException("Attempting to create the absolute of a term which is not of integer sort");          
  }

  Symbol abs = interpretedSymbol(Kernel::Theory::INT_ABS, _aux);
  return term(abs, t1);
}

Expression FormulaBuilder::geq(const Expression& t1, const Expression& t2)
{
  CALL("FormulaBuilder::geq");

  checkForNumericalSortError({t1, t2});
  
  Symbol geq;
  if(t1.sort() == integerSort()){
    geq = interpretedSymbol(Kernel::Theory::INT_GREATER_EQUAL, _aux);
  } else if(t1.sort() == realSort()){
    geq = interpretedSymbol(Kernel::Theory::REAL_GREATER_EQUAL, _aux);
  } else {
    geq = interpretedSymbol(Kernel::Theory::RAT_GREATER_EQUAL, _aux);
  } 
  return term(geq, t1, t2);
}

Expression FormulaBuilder::leq(const Expression& t1, const Expression& t2)
{
  CALL("FormulaBuilder::leq");

  checkForNumericalSortError({t1, t2});
  
  Symbol leq;
  if(t1.sort() == integerSort()){
    leq = interpretedSymbol(Kernel::Theory::INT_LESS_EQUAL, _aux);
  } else if(t1.sort() == realSort()){
    leq = interpretedSymbol(Kernel::Theory::REAL_LESS_EQUAL, _aux);
  } else {
    leq = interpretedSymbol(Kernel::Theory::RAT_LESS_EQUAL, _aux);
  } 
  return term(leq, t1, t2);
}

Expression FormulaBuilder::gt(const Expression& t1, const Expression& t2)
{
  CALL("FormulaBuilder::gt");

  checkForNumericalSortError({t1, t2});
  
  Symbol gt;
  if(t1.sort() == integerSort()){
    gt = interpretedSymbol(Kernel::Theory::INT_GREATER, _aux);
  } else if(t1.sort() == realSort()){
    gt = interpretedSymbol(Kernel::Theory::REAL_GREATER, _aux);
  } else {
    gt = interpretedSymbol(Kernel::Theory::RAT_GREATER, _aux);
  } 
  return term(gt, t1, t2);
}

Expression FormulaBuilder::lt(const Expression& t1, const Expression& t2)
{
  CALL("FormulaBuilder::lt");

  checkForNumericalSortError({t1, t2});
  
  Symbol lt;
  if(t1.sort() == integerSort()){
    lt = interpretedSymbol(Kernel::Theory::INT_LESS, _aux);
  } else if(t1.sort() == realSort()){
    lt = interpretedSymbol(Kernel::Theory::REAL_LESS, _aux);
  } else {
    lt = interpretedSymbol(Kernel::Theory::RAT_LESS, _aux);
  } 
  return term(lt, t1, t2);
}  

Expression FormulaBuilder::store(const Expression& array, const Expression& index, const Expression& newVal)
{
  CALL("FormulaBuilder::store");

  if(!array.sort().isArraySort()){
    throw ApiException("Attempting to store in non-array!");          
  }
  if(index.sort() != array.sort().indexSort()){
    throw ApiException("Failed due to sort of index not matching index sort of array");
  }
  if(newVal.sort() != array.sort().innerSort()){
    throw ApiException("Failed due to sort of newVal not matching inner sort of array");              
  }

  OperatorType* funType = Theory::getArrayOperatorType(array.sort(),Theory::ARRAY_STORE);
  unsigned fun = env.signature->getInterpretingSymbol(Theory::ARRAY_STORE,funType);
  Symbol store(fun, false, _aux);

  return term(store, array, index, newVal);
}


Expression FormulaBuilder::select(const Expression& array, const Expression& index)
{
  CALL("FormulaBuilder::select");

  if(!array.sort().isArraySort()){
    throw ApiException("Attempting to select from a non-array!");          
  }
  if(index.sort() != array.sort().indexSort()){
    throw ApiException("Failed due to sort of index not matching index sort of array");
  }

  bool predicate = array.sort().innerSort() == boolSort();

  OperatorType* funType = predicate ? Theory::getArrayOperatorType(array.sort(),Theory::ARRAY_BOOL_SELECT)
                                    : Theory::getArrayOperatorType(array.sort(),Theory::ARRAY_SELECT);
                                    
  unsigned fun = predicate ? env.signature->getInterpretingSymbol(Theory::ARRAY_BOOL_SELECT,funType)
                           : env.signature->getInterpretingSymbol(Theory::ARRAY_SELECT,funType);
 
  Symbol select(fun, predicate, _aux);

  return term(select, array, index);
}

//////////////////////////////
// Wrapper implementation


Sort::Sort(Kernel::TermList s)
{
  _content=s.content();
}

Sort::Sort(Kernel::TermList s, ApiHelper aux) : _aux(aux)
{
  _content=s.content();
}

bool Sort::isVar() const
{
  CALL("Sort::isVar");

  return static_cast<Kernel::TermList>(*this).isVar();
} 

Sort Sort::getInvalid()
{
  CALL("Sort::getInvalid");
  
  static TermList t;
  t.makeEmpty();
  return Sort(t);
}

// not sure about the isVar part...
bool Sort::isValid() const
{ 
  CALL("Sort::isValid");

  Kernel::TermList sort = static_cast<Kernel::TermList>(*this);

  return !sort.isEmpty() && 
         (sort.isVar() || env.signature->isNonDefaultCon(sort.term()->functor()) || _aux->isValid()); 
}

bool Sort::isTupleSort() const
{
  CALL("Sort::isTupleSort");
  
  if(!isValid()){ return false; }

  return static_cast<Kernel::TermList>(*this).isTupleSort();
}

bool Sort::isArraySort() const
{
  CALL("Sort::isArraySort");

  if(!isValid()){ return false; }

  return static_cast<Kernel::TermList>(*this).isArraySort();
}

bool Sort::isBoolSort() const
{
  CALL("Sort::isBoolSort");

  if(!isValid()){ return false; }

  return static_cast<Kernel::TermList>(*this).isBoolSort();
}

std::string Sort::toString() const
{
  CALL("Sort::toString");

  if(!isValid()){
    throw ApiException("Sort created prior to hard solver reset and cannot be printed");    
  }
  return StringUtils::copy2str(_aux->toString(static_cast<Kernel::TermList>(*this)));
}


Sort Sort::indexSort() const
{
  CALL("Sort::indexSort");
   
  if(!isValid()){
    throw ApiException("Cannot get the index sort of a sort created prior to a hard solver reset");        
  }
  if(!isArraySort()){
    throw ApiException("Cannot get the index sort of a sort of a non-array sort");        
  }
  Sort index(*static_cast<Kernel::TermList>(*this).term()->nthArgument(0));
  index._aux=_aux;
  return index;  
}

Sort Sort::innerSort() const
{
  CALL("Sort::indexSort");
   
  if(!isValid()){
    throw ApiException("Cannot get the inner sort of a sort created prior to a hard solver reset");        
  }
  if(!isArraySort()){
    throw ApiException("Cannot get the inner sort of a sort of a non-array sort");        
  }
  Sort inner(*static_cast<Kernel::TermList>(*this).term()->nthArgument(1));
  inner._aux=_aux;
  return inner;  
}

unsigned Sort::arity() const
{
  CALL("Sort::arity");

  if(!isValid()){ 
    throw ApiException("Cannot get the arity of a sort created prior to a hard solver reset");    
  }

  if(isVar()){
    throw ApiException("Cannot get the arity of a variable sort");        
  }

  return static_cast<Kernel::TermList>(*this).term()->arity();
}


Sort::operator Kernel::TermList() const
{  
  return TermList(_content);
}

bool Sort::operator==(const Sort& s) const
{
  return _content == s._content;
}

bool Sort::operator!=(const Sort& s) const
{
  return !(*this == s);
}

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

string Expression::toString() const
{
  CALL("Expression::toString");

  if(isNull()) {
    throw ApiException("Expression not initialized");
  }
  if(!isValid()){
    throw ApiException("Expression created prior to hard solver reset and cannot be printed");    
  }
  if(isTerm()){
    return StringUtils::copy2str(_aux->toString(static_cast<Kernel::TermList>(*this)));
  }
  return StringUtils::copy2str(static_cast<Kernel::Formula*>(*this)->toString());
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

bool Expression::isIte() const
{
  CALL("Expression::isIte");

  if(isNull()) {
    throw ApiException("Expression not initialized");
  }
  if(!isTerm()){
    return false;
  }
  TermList tl = static_cast<Kernel::TermList>(*this);
  return tl.isTerm() && tl.term()->isSpecial() && 
         tl.term()->getSpecialData()->getType() == Term::SF_ITE;  
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
  if(isIte()){
    return Sort(static_cast<Kernel::TermList>(*this).term()->getSpecialData()->getSort(), _aux);
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

/*StringIterator Expression::freeVars()
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

  VList* vars=  _form->freeVariables();
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

  VList* vars=_form->boundVariables();

  return _aux->getVarNames(vars);
}*/

string AnnotatedFormula::toString() const
{
  CALL("AnnotatedFormula::toString");

  if(!isValid()){
    throw ApiException("Cannot print a formula created prior to a hard solver reset");    
  }
  return StringUtils::copy2str(unit->toString());
}

string AnnotatedFormula::name() const
{
  CALL("AnnotatedFormula::toString");

  vstring unitName;
  if(!Parse::TPTP::findAxiomName(unit, unitName)) {
    unitName="u" + Int::toString(unit->number());
  }
  return StringUtils::copy2str(unitName);
}

bool AnnotatedFormula::isValid() const
{ return _aux->isValid(); }

/*StringIterator AnnotatedFormula::freeVars()
{
  CALL("AnnotatedFormula::freeVars");

  if(!isValid()){
    throw ApiException("Free variables cannot be retrieved from a formula created prior to a hard solver reset");    
  }
  if(!unit) {
    return StringIterator(VirtualIterator<vstring>::getEmpty());
  }
  VList* vl=0;
  if(unit->isClause()) {
    VList::pushFromIterator(static_cast<Clause*>(unit)->getVariableIterator(), vl);
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
  VList* vl=static_cast<FormulaUnit*>(unit)->formula()->boundVariables();
  return _aux->getVarNames(vl);
}*/

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

void AnnotatedFormula::assignName(AnnotatedFormula& form, string name)
{
  CALL("AnnotatedFormula::assignName");

  if(!form.isValid()){
    throw ApiException("Cannot assign a name to a formula created prior to a hard solver reset");    
  }

  if(!OutputOptions::assignFormulaNames()) {
    return;
  }

  vstring vname = StringUtils::copy2vstr(name);

  static DHSet<vstring> usedNames;

  if(!usedNames.insert(vname)) {
    vstring name0 = vname;
    unsigned idx = 0;
    do {
      idx++;
      vname = name0 + "_" + Int::toString(idx);
    } while(!usedNames.insert(vname));
  }

  Parse::TPTP::assignAxiomName(form.unit, vname);
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

/*StringIterator::StringIterator(const VirtualIterator<vstring>& vit)
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
}*/

} //namespace Api


//////////////////////////////
// Output implementation

std::ostream& operator<< (std::ostream& str,const Vampire::Sort& sort)
{
  CALL("operator<< (ostream&,const Vampire::Sort&)");
  return str<<sort.toString();
}

ostream& operator<< (ostream& str,const Vampire::Expression& f)
{
  CALL("operator<< (ostream&,const Vampire::Expression&)");
  return str<<f.toString();
}

ostream& operator<< (ostream& str,const Vampire::AnnotatedFormula& af)
{
  CALL("operator<< (ostream&,const Vampire::AnnotatedFormula&)");
  return str<<af.toString();
}

