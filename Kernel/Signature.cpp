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
 * @file Signature.cpp
 * Implements class Signature for handling signatures
 */

#include "Debug/Assertion.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Kernel/NumTraits.hpp"
#include "Shell/Options.hpp"
#include "Kernel/SortHelper.hpp"

#include "Signature.hpp"

using namespace std;
using namespace Kernel;
using namespace Shell;

const unsigned Signature::STRING_DISTINCT_GROUP = 0;

/**
 * Standard constructor.
 * @author Andrei Voronkov
 */
Signature::Symbol::Symbol(const std::string& nm, unsigned arity, bool interpreted, bool preventQuoting, bool super)
  : _name(nm),
    _arity(arity),
    _typeArgsArity(0),
    _type(0),
    _distinctGroups(0),
    _usageCount(0),
    _unitUsageCount(0),
    _interpreted(interpreted ? 1 : 0),
    _linMul(0),
    _introduced(0),
    _protected(0),
    _skip(0),
    _label(0),
    _equalityProxy(0),
    _wasFlipped(0),
    _color(COLOR_TRANSPARENT),
    _answerPredicate(0),
    _termAlgebraCons(0),
    _termAlgebraDest(0),
    _inGoal(0),
    _inUnit(0),
    _inductionSkolem(0),
    _skolem(0),
    _skipCongruence(0),
    _tuple(0),
    _computable(1),
    _letBound(0),
    _prox(NOT_PROXY),
    _comb(NOT_COMB)
{
  if (!preventQuoting && symbolNeedsQuoting(_name, interpreted,arity)) {
    _name="'"+_name+"'";
  }
  if (_interpreted || isProtectedName(nm)) {
    markProtected();
  }
} // Symbol::Symbol

/**
 * Deallocate function Symbol object
 */
void Signature::Symbol::destroyFnSymbol()
{
  if (integerConstant()) {
    delete static_cast<IntegerSymbol*>(this);
  }
  else if (rationalConstant()) {
    delete static_cast<RationalSymbol*>(this);
  }
  else if (realConstant()) {
    delete static_cast<RealSymbol*>(this);
  }
  else if (interpreted()) {
    delete static_cast<InterpretedSymbol*>(this);
  }
  else if (linMul()) {
    forAnyNumTraits([&](auto n) {
        if (auto s = Signature::tryLinMulSym<typename decltype(n)::ConstantType>(this)) {
          delete &*s;
          return true;
        } else {
          return false;
        }
    });
  }
  else {
    delete this;
  }
}

/**
 * Deallocate predicate Symbol object
 */
void Signature::Symbol::destroyPredSymbol()
{
  if (interpreted()) {
    delete static_cast<InterpretedSymbol*>(this);
  }
  else {
    delete this;
  }
}

void Signature::Symbol::destroyTypeConSymbol()
{
  ASS(!interpreted());

  delete this;
}

/**
 * Add constant symbol into a distinct group
 *
 * A constant can be added into one particular distinct group
 * at most once
 *
 * We also record the symbol in the group's members
 */
void Signature::Symbol::addToDistinctGroup(unsigned group,unsigned this_number)
{
  ASS_EQ(arity(), 0);
  ASS(!List<unsigned>::member(group, _distinctGroups))

  List<unsigned>::push(group, _distinctGroups);
  env.signature->_distinctGroupsAddedTo=true;

  Signature::DistinctGroupMembers members = env.signature->_distinctGroupMembers[group];
  members->push(this_number);
} // addToDistinctGroup

/**
 * Set type of the symbol
 *
 * The type can be set only once for each symbol, and if the type
 * should be different from the default type, this function must be
 * called before any call to @c fnType(), @c predType() or @c typeConType().
 */
void Signature::Symbol::setType(OperatorType* type)
{
  ASS_REP(!_type || _type == type, _type->toString());

  // this is copied out to the Symbol for convenience
  _typeArgsArity = type->numTypeArguments(); 
  _type = type;
}

/**
 * This force the type to change
 * This can be unsafe so should only be used when you know it is safe to
 * change the type i.e. nothing yet relies on the type of this symbol
 */
void Signature::Symbol::forceType(OperatorType* type)
{
  if(_type){ delete _type; }
  _type = type;
}

/**
 * Return the type of a function symbol
 *
 * If the @c setType() function was not called before, the function
 * symbol is assigned a default type.
 */
OperatorType* Signature::Symbol::fnType() const
{
  if (!_type) {
    TermList def = AtomicSort::defaultSort();
    _type = OperatorType::getFunctionTypeUniformRange(arity(), def, def);
  }
  return _type;
}

/**
 * Return the type of a typeConType symbol
 *
 * If the @c setType() function was not called before, the function
 * symbol is assigned a default type.
 */
OperatorType* Signature::Symbol::typeConType() const
{
  if (!_type) {
    _type = OperatorType::getTypeConType(arity());
  }
  return _type;
}

/**
 * Return the type of a predicate symbol
 *
 * If the @c setType() function was not called before, the function
 * symbol is assigned a default type.
 */
OperatorType* Signature::Symbol::predType() const
{
  if (!_type) {
    TermList def = AtomicSort::defaultSort();
    _type = OperatorType::getPredicateTypeUniformRange(arity(), def);
  }
  return _type;
}


/**
 * Create a Signature.
 * @since 07/05/2007 Manchester
 * @since 04/05/2015 Gothenburg -- add true and false
 */
Signature::Signature ():
    _foolConstantsDefined(false), _foolTrue(0), _foolFalse(0),
    _funs(32),
    _preds(32),
    _typeCons(32),
    _nextFreshSymbolNumber(0),
    _skolemFunctionCount(0),
    _distinctGroupsAddedTo(false),
    _strings(0),
    _integers(0),
    _rationals(0),
    _reals(0),
    _arrayCon(UINT_MAX),
    _arrowCon(UINT_MAX),
    _appFun(UINT_MAX),
    _termAlgebras()
{
  ALWAYS(createDistinctGroup() == STRING_DISTINCT_GROUP);
} // Signature::Signature

/* Adding equality predicate used to be carried out in the constructor.
 * However now that sorts are TermLists, this involves a call to Signature
 * from AtomicSort::defaultSort before the Signature has been constructed. hence
 * the function below
 */
void Signature::addEquality()
{
  // initialize equality
  addInterpretedPredicate(Theory::EQUAL, OperatorType::getPredicateType(2), "=");
  ASS_EQ(predicateName(0), "="); //equality must have number 0
  getPredicate(0)->markSkip();
}

/**
 * Destroy a Signature.
 * @since 07/05/2007 Manchester
 */
Signature::~Signature ()
{
  for (int i = _funs.length()-1;i >= 0;i--) {
    _funs[i]->destroyFnSymbol();
  }
  for (int i = _preds.length()-1;i >= 0;i--) {
    _preds[i]->destroyPredSymbol();
  }
  for (int i = _typeCons.length()-1;i >= 0;i--) {
    _typeCons[i]->destroyTypeConSymbol();
  }
} // Signature::~Signature

/**
 * Add interpreted function
 */
unsigned Signature::addInterpretedFunction(Interpretation interpretation, OperatorType* type, const std::string& name)
{
  ASS(Theory::isFunction(interpretation));

  Theory::MonomorphisedInterpretation mi = std::make_pair(interpretation,type);

  unsigned res;
  if (_iSymbols.find(mi,res)) { // already declared
    // TODO should this really be done in release mode?
    if (name!=functionName(res)) {
      USER_ERROR("Interpreted function '"+functionName(res)+"' has the same interpretation as '"+name+"' should have");
    }
    return res;
  }

  auto symbolKey = SymbolKey(std::make_pair(interpretation, type));
  ASS_REP(!_funNames.find(symbolKey), name);

  unsigned fnNum = _funs.length();
  InterpretedSymbol* sym = new InterpretedSymbol(name, interpretation);
  _funs.push(sym);
  _funNames.insert(symbolKey, fnNum);
  ALWAYS(_iSymbols.insert(mi, fnNum));

  OperatorType* fnType = type;
  ASS(fnType->isFunctionType());
  sym->setType(fnType);
  return fnNum;
} // Signature::addInterpretedFunction

/**
 * Add interpreted predicate
 */
unsigned Signature::addInterpretedPredicate(Interpretation interpretation, OperatorType* type, const std::string& name)
{
  ASS(!Theory::isFunction(interpretation));

  // cout << "addInterpretedPredicate " << (type ? type->toString() : "nullptr") << " " << name << endl;

  Theory::MonomorphisedInterpretation mi = std::make_pair(interpretation,type);

  unsigned res;
  if (_iSymbols.find(mi,res)) { // already declared
    if (name!=predicateName(res)) {
      USER_ERROR("Interpreted predicate '"+predicateName(res)+"' has the same interpretation as '"+name+"' should have");
    }
    return res;
  }

  auto symbolKey = SymbolKey(std::make_pair(interpretation, type));

  // cout << "symbolKey " << symbolKey << endl;

  ASS_REP(!_predNames.find(symbolKey), symbolKey);

  unsigned predNum = _preds.length();
  InterpretedSymbol* sym = new InterpretedSymbol(name, interpretation);
  _preds.push(sym);
  _predNames.insert(symbolKey,predNum);
  ALWAYS(_iSymbols.insert(mi, predNum));
  if (predNum!=0) {
    OperatorType* predType = type;
    ASS_REP(!predType->isFunctionType(), predType->toString());
    sym->setType(predType);
  }
  return predNum;
} // Signature::addInterpretedPredicate


/**
 * Return number of symbol that is interpreted by Interpretation @b interp.
 *
 * If no such symbol exists, it is created.
 */
unsigned Signature::getInterpretingSymbol(Interpretation interp, OperatorType* type)
{
  Theory::MonomorphisedInterpretation mi = std::make_pair(interp,type);

  unsigned res;
  if (_iSymbols.find(mi, res)) {
    return res;
  }

  std::string name = theory->getInterpretationName(interp);
  unsigned arity = Theory::getArity(interp);
  
  if (Theory::isFunction(interp)) {
    if (functionExists(name, arity)) {
      int i=0;
      while(functionExists(name+Int::toString(i), arity)) {
        i++;
      }
      name=name+Int::toString(i);
    }
    addInterpretedFunction(interp, type, name);
  }
  else {
    if (predicateExists(name, arity)) {
      int i=0;
      while(predicateExists(name+Int::toString(i), arity)) {
        i++;
      }
      name=name+Int::toString(i);
    }
    addInterpretedPredicate(interp, type, name);
  }

  //we have now registered a new function, so it should be present in the map
  return _iSymbols.get(mi);
}

const std::string& Signature::functionName(int number)
{
  // it is safe to reuse "$true" and "$false" for constants
  // because the user cannot define constants with these names herself
  // and the formula, obtained by toString() with "$true" or "$false"
  // in term position would be syntactically valid in FOOL
  if (!env.options->showFOOL() && isFoolConstantSymbol(false,number)) {
    static std::string fols("$false");
    return fols;
  }
  if (!env.options->showFOOL() && isFoolConstantSymbol(true,number)) { 
    static std::string troo("$true");
    return troo;
  }
  return _funs[number]->name();
}

/**
 * Return true if specified function exists
 */
bool Signature::functionExists(const std::string& name,unsigned arity) const
{
  return _funNames.find(key(name, arity));
}

/**
 * Return true if specified predicate exists
 */
bool Signature::predicateExists(const std::string& name,unsigned arity) const
{
  return _predNames.find(key(name, arity));
}

/**
 * Return true if specified type constructor exists
 */
bool Signature::typeConExists(const std::string& name,unsigned arity) const
{
  return _typeConNames.find(key(name, arity));
}

unsigned Signature::getFunctionNumber(const std::string& name, unsigned arity) const
{
  ASS(_funNames.find(key(name, arity)));
  return _funNames.get(key(name, arity));
}

bool Signature::tryGetFunctionNumber(const std::string& name, unsigned arity, unsigned& out) const
{
  auto* value = _funNames.getPtr(key(name, arity));
  if (value != NULL) {
    out = *value;
    return true;
  } else {
    return false;
  }
}

bool Signature::tryGetPredicateNumber(const std::string& name, unsigned arity, unsigned& out) const
{
  auto* value = _predNames.getPtr(key(name, arity));
  if (value != NULL) {
    out = *value;
    return true;
  } else {
    return false;
  }
}


unsigned Signature::getPredicateNumber(const std::string& name, unsigned arity) const
{
  ASS(_predNames.find(key(name, arity)));
  return _predNames.get(key(name, arity));
}

/**
 * If a function with this name and arity exists, return its number.
 * Otherwise, add a new one and return its number.
 *
 * @param name name of the symbol
 * @param arity arity of the symbol
 * @param added will be set to true if the function did not exist
 * @since 07/05/2007 Manchester
 */
unsigned Signature::addFunction (const std::string& name,
				 unsigned arity,
				 bool& added)
{
  auto symbolKey = key(name,arity);
  unsigned result;
  if (_funNames.find(symbolKey,result)) {
    added = false;
    getFunction(result)->unmarkIntroduced();
    return result;
  }
  if (env.options->arityCheck()) {
    unsigned prev;
    if (_arityCheck.find(name,prev)) {
      unsigned prevArity = prev/2;
      bool isFun = prev % 2;
      USER_ERROR((std::string)"Symbol " + name +
		 " is used both as a function of arity " + Int::toString(arity) +
		 " and a " + (isFun ? "function" : "predicate") +
		 " of arity " + Int::toString(prevArity));
    }
    _arityCheck.insert(name,2*arity+1);
  }

  result = _funs.length();
  bool super = (name == "$tType");
  _funs.push(new Symbol(name, arity, 
        /*       interpreted */ false, 
        /*    preventQuoting */ super, 
                                super));
  _funNames.insert(symbolKey, result);
  added = true;
  return result;
} // Signature::addFunction

/**
 * Add a string constant to the signature. This constant will automatically be
 * added to the distinct group STRING_DISTINCT_GROUP.
 * @author Andrei Voronkov
 */
unsigned Signature::addStringConstant(const std::string& name)
{
  auto symbolKey = SymbolKey(name);
  unsigned result;
  if (_funNames.find(symbolKey,result)) {
    return result;
  }

  _strings++;
  // TODO shouldn't we also quote inside of name?
  std::string quotedName = "\"" + name + "\"";
  result = _funs.length();
  Symbol* sym = new Symbol(quotedName,
        /*             arity */ 0, 
        /*       interpreted */ false, 
        /*    preventQuoting */ true, 
        /*             super */ false);
  sym->addToDistinctGroup(STRING_DISTINCT_GROUP,result);
  _funs.push(sym);
  _funNames.insert(symbolKey,result);
  return result;
} // addStringConstant


unsigned Signature::getApp()
{
  bool added = false;
  unsigned app = addFunction("vAPP", 4, added);
  if(added){
    _appFun = app;
    TermList tv1 = TermList(0, false);
    TermList tv2 = TermList(1, false);
    TermList arrowType = AtomicSort::arrowSort(tv1, tv2);
    OperatorType* ot = OperatorType::getFunctionType({arrowType, tv1}, tv2, 2);
    Symbol* sym = getFunction(app);
    sym->setType(ot);
  }
  return app;
}

unsigned Signature::getDiff(){
  bool added = false;
  unsigned diff = addFunction("diff",2, added);      
  if(added){
    TermList alpha = TermList(0, false);
    TermList beta = TermList(1, false);
    TermList alphaBeta = AtomicSort::arrowSort(alpha, beta);
    TermList result = AtomicSort::arrowSort(alphaBeta, alphaBeta, alpha);
    Symbol * sym = getFunction(diff);
    sym->setType(OperatorType::getConstantsType(result, 2));
  }
  return diff;
}


unsigned Signature::getFnDef(unsigned fn)
{
  auto type = getFunction(fn)->fnType();
  auto sort = type->result();
  bool added = false;
  auto name = "sFN_"+getFunction(fn)->name();
  unsigned p = addPredicate(name, 2+type->numTypeArguments(), added);
  if (added) {
    ALWAYS(_fnDefPreds.insert(p));
    OperatorType* ot = OperatorType::getPredicateType({sort, sort}, type->numTypeArguments());
    Symbol* sym = getPredicate(p);
    sym->markProtected();
    sym->setType(ot);
  }
  return p;
}

unsigned Signature::getBoolDef(unsigned fn)
{
  auto type = getPredicate(fn)->predType();
  auto name = "sPN_"+getPredicate(fn)->name();
  bool added = false;
  auto p = addPredicate(name, type->arity(), added);
  if (added) {
    ALWAYS(_boolDefPreds.insert(p,fn));
    TermStack sorts;
    for (unsigned i = type->numTypeArguments(); i < type->arity(); i++) {
      sorts.push(type->arg(i));
    }
    OperatorType* ot = OperatorType::getPredicateType(sorts.size(), sorts.begin(), type->numTypeArguments());
    Symbol* sym = getPredicate(p);
    sym->markProtected();
    sym->setType(ot);
  }
  return p;
}

unsigned Signature::getChoice(){
  bool added = false;
  unsigned choice = addFunction("vEPSILON",1, added);      
  if(added){
    TermList alpha = TermList(0, false);
    TermList bs = AtomicSort::boolSort();
    TermList alphaBs = AtomicSort::arrowSort(alpha, bs);
    TermList result = AtomicSort::arrowSort(alphaBs, alpha);
    Symbol * sym = getFunction(choice);
    sym->setType(OperatorType::getConstantsType(result, 1));
  }
  return choice;
}

void Signature::incrementFormulaCount(Term* t){
  ASS(SortHelper::getResultSort(t) == AtomicSort::boolSort());

  if(_formulaCounts.find(t)){
    int count =  _formulaCounts.get(t);
    if(count != -1){
      _formulaCounts.set(t, count + 1);
    }
  } else {
    _formulaCounts.set(t, 1);
  }
}

void Signature::decrementFormulaCount(Term* t){
  ASS(SortHelper::getResultSort(t) == AtomicSort::boolSort());

  ASS(_formulaCounts.find(t))
  int count = _formulaCounts.get(t);
  if(count != -1){
    _formulaCounts.set(t, count - 1);
  }
}

void Signature::formulaNamed(Term* t){
  ASS(SortHelper::getResultSort(t) == AtomicSort::boolSort());

  ASS(_formulaCounts.find(t));
  _formulaCounts.set(t, -1);
}

unsigned Signature::formulaCount(Term* t){
  if(_formulaCounts.find(t)){
    return _formulaCounts.get(t);
  }
  return 0;
}


/**
 * If a type constructor with this name and arity exists, return its number.
 * Otherwise, add a new one and return its number.
 */
unsigned Signature::addTypeCon (const std::string& name,
         unsigned arity,
         bool& added)
{
  auto symbolKey = key(name,arity);
  unsigned result;
  if (_typeConNames.find(symbolKey,result)) {
    added = false;
    return result;
  }
  //TODO no arity check. Is this safe?

  result = _typeCons.length();
  _typeCons.push(new Symbol(name,arity, /* interpreted */ false, /* preventQuoting */ false, /* super */ false));
  _typeConNames.insert(symbolKey,result);
  added = true;
  return result;
}

/**
 * If a predicate with this name and arity exists, return its number.
 * Otherwise, add a new one and return its number.
 *
 * @param name name of the symbol
 * @param arity arity of the symbol
 * @param added set to true if a new predicate has been added, and false
 *        otherwise
 * @since 07/05/2007 Manchester
 * @since 08/07/2007 Manchester, adds parameter added
 * @since 06/12/2009 Haifa, arity check added
 * @author Andrei Voronkov
 */
unsigned Signature::addPredicate (const std::string& name,
				  unsigned arity,
				  bool& added)
{
  auto symbolKey = key(name,arity);
  unsigned result;
  if (_predNames.find(symbolKey,result)) {
    added = false;
    getPredicate(result)->unmarkIntroduced();
    return result;
  }
  if (env.options->arityCheck()) {
    unsigned prev;
    if (_arityCheck.find(name,prev)) {
      unsigned prevArity = prev/2;
      bool isFun = prev % 2;
      USER_ERROR((std::string)"Symbol " + name +
		 " is used both as a predicate of arity " + Int::toString(arity) +
		 " and a " + (isFun ? "function" : "predicate") +
		 " of arity " + Int::toString(prevArity));
    }
    _arityCheck.insert(name,2*arity);
  }

  result = _preds.length();
  _preds.push(new Symbol(name, arity, 
        /*       interpreted */ false, 
        /*    preventQuoting */ false, 
        /*             super */ false));
  _predNames.insert(symbolKey,result);
  added = true;
  return result;
} // Signature::addPredicate

/**
 * Create a new name.
 * @since 01/07/2005 Manchester
 */
unsigned Signature::addNamePredicate(unsigned arity)
{
  return addFreshPredicate(arity,"sP");
} // addNamePredicate


unsigned Signature::addNameFunction(unsigned arity)
{
  return addFreshFunction(arity,"sP");
} // addNameFunction

/**
 * Add fresh function of a given arity and with a given prefix. If suffix is non-zero,
 * the function name will be prefixI, where I is an integer, otherwise it will be
 * prefixI_suffix. The new function will be marked as skip for the purpose of equality
 * elimination.
 */
unsigned Signature::addFreshFunction(unsigned arity, const char* prefix, const char* suffix)
{
  std::string pref(prefix);
  std::string suf(suffix ? std::string("_")+suffix : "");
  bool added;
  unsigned result;
  //commented out because it could lead to introduction of function with the same name
  //that differ only in arity (which is OK with tptp, but iProver was complaining when
  //using Vampire as clausifier)
//  unsigned result = addFunction(pref+suf,arity,added);
//  if (!added) {
    do {
      result = addFunction(pref+Int::toString(_nextFreshSymbolNumber++)+suf,arity,added);
    }
    while (!added);
//  }
  Symbol* sym = getFunction(result);
  sym->markIntroduced();
  sym->markSkip();
  return result;
} // addFreshFunction

/**
 * Add fresh typeCon of a given arity and with a given prefix. If suffix is non-zero,
 * the typeCon name will be prefixI, where I is an integer, otherwise it will be
 * prefixI_suffix. The new function will be marked as skip for the purpose of equality
 * elimination.
 */
unsigned Signature::addFreshTypeCon(unsigned arity, const char* prefix, const char* suffix)
{
  std::string pref(prefix);
  std::string suf(suffix ? std::string("_")+suffix : "");
  bool added;
  unsigned result;

  do {
    result = addTypeCon(pref+Int::toString(_nextFreshSymbolNumber++)+suf,arity,added);
  }
  while (!added);

  Symbol* sym = getTypeCon(result);
  //TODO are these necessary? I doubt that equality elimination works
  //on sorts anyway. Requires further investigation.
  sym->markIntroduced();
  sym->markSkip();
  return result;
} // addFreshFunction

/**
 * Add fresh predicate of a given arity and with a given prefix. If suffix is non-zero,
 * the predicate name will be prefixI, where I is an integer, otherwise it will be
 * prefixI_suffix. The new predicate will be marked as skip for the purpose of equality
 * elimination.
 */
unsigned Signature::addFreshPredicate(unsigned arity, const char* prefix, const char* suffix)
{
  std::string pref(prefix);
  std::string suf(suffix ? std::string("_")+suffix : "");
  bool added = false;
  unsigned result;
  //commented out because it could lead to introduction of function with the same name
  //that differ only in arity (which is OK with tptp, but iProver was complaining when
  //using Vampire as clausifier)
//  if (suffix) {
//    result = addPredicate(pref+suf,arity,added);
//  }
//  if (!added) {
    do {
      result = addPredicate(pref+Int::toString(_nextFreshSymbolNumber++)+suf,arity,added);
    }
    while (!added);
//  }
  Symbol* sym = getPredicate(result);
  sym->markIntroduced();
  sym->markSkip();
  return result;
} // addFreshPredicate

/**
 * Return a new Skolem function. If @b suffix is nonzero, include it
 * into the name of the Skolem function.
 * @since 01/07/2005 Manchester
 */
unsigned Signature::addSkolemFunction (unsigned arity, const char* suffix, bool computable)
{
  unsigned f = addFreshFunction(arity, "sK", suffix);
  Symbol* s = getFunction(f);
  s->markSkolem();
  if (!computable) {
    s->markUncomputable();
  }

  // Register it as a LaTeX function
 // theory->registerLaTeXFuncName(f,"\\sigma_{"+Int::toString(_skolemFunctionCount)+"}(a0)");
  _skolemFunctionCount++;

  return f;
} // addSkolemFunction

/**
 * Return a new Skolem typeCon. If @b suffix is nonzero, include it
 * into the name of the Skolem typeCon.
 * @since 01/07/2005 Manchester
 */
unsigned Signature::addSkolemTypeCon (unsigned arity, const char* suffix)
{
  unsigned tc = addFreshTypeCon(arity, "sK", suffix);
  getTypeCon(tc)->markSkolem();

  // Register it as a LaTeX function
 // theory->registerLaTeXFuncName(f,"\\sigma_{"+Int::toString(_skolemFunctionCount)+"}(a0)");
  _skolemFunctionCount++;

  return tc;
} // addSkolemFunction


/**
 * Return a new Skolem predicate. If @b suffix is nonzero, include it
 * into the name of the Skolem function.
 * @since 15/02/2016 Gothenburg
 */
unsigned Signature::addSkolemPredicate(unsigned arity, const char* suffix)
{
  unsigned p = addFreshPredicate(arity, "sK", suffix);
  getPredicate(p)->markSkolem();

  // Register it as a LaTeX function
 // theory->registerLaTeXFuncName(f,"\\sigma_{"+Int::toString(_skolemFunctionCount)+"}(a0)");
  _skolemFunctionCount++;

  return p;
} // addSkolemPredicate

/**
 * Return the key "name_arity" used for hashing. This key is obtained by
 * concatenating the name, underscore character and the arity. The key is
 * created in such a way that it does not collide with special keys, such as
 * those for string constants.
 * @since 27/02/2006 Redmond
 * @author Andrei Voronkov
 */
Signature::SymbolKey Signature::key(const std::string& name,int arity)
{
  return SymbolKey(std::make_pair(name,unsigned(arity)));
} // Signature::key


/** Add a color to the symbol for interpolation and symbol elimination purposes */
void Signature::Symbol::addColor(Color color)
{
  ASS_L(color,3);
  ASS_G(color,0);
  ASS(env.colorUsed);

  if (_color && color != static_cast<Color>(_color)) {
    USER_ERROR("A symbol cannot have two colors");
  }
  _color = color;
} // addColor

/**
 * Create a group of distinct elements. @c premise should contain
 * the unit that declared the distinct group, or zero if there isn't any.
 */
unsigned Signature::createDistinctGroup(Unit* premise)
{
  unsigned res = _distinctGroupPremises.size();
  _distinctGroupPremises.push(premise);
  // DistinctGroupMember stack = ;
  _distinctGroupMembers.push(DistinctGroupMembers(new Stack<unsigned>));
  return res;
}

/**
 * Return premise of the distinct group, or 0 if the distinct group doesn't have any
 */
Unit* Signature::getDistinctGroupPremise(unsigned group)
{
  return _distinctGroupPremises[group];
}

/**
 * Add a constant into a group of distinct elements
 *
 * One constant can be added into one particular distinct group only once.
 */
void Signature::addToDistinctGroup(unsigned constantSymbol, unsigned groupId)
{
  Symbol* sym = getFunction(constantSymbol);
  sym->addToDistinctGroup(groupId,constantSymbol);
}

bool Signature::isProtectedName(std::string name)
{
  if (name=="$distinct") {
    //TODO: remove this hack once we properly support the $distinct predicate
    return true;
  }

  std::string protectedPrefix = env.options->protectedPrefix();
  if (protectedPrefix.size()==0) {
    return false;
  }
  if (name.substr(0, protectedPrefix.size())==protectedPrefix) {
    return true;
  }
  return false;
}

/**
 * Return true if specified symbol should be quoted in the TPTP syntax.
 * This function does not apply to integer or string constants. It only
 * applies during parsing, it is not used when the symbol is printed:
 * when it is printed, its saved name will already be quoted.
 *
 * The function charNeedsQuoting determines characters whose presence in
 * the symbol name implies that they should be quoted. There are however
 * several exceptions to it:
 *
 * Equality is not quoted
 *
 * Numbers are not quoted. However names that just look like numbers
 * are quoted (the distinction is that these are not interpreted)
 *
 * $distinct predicate is not quoted
 *
 * $true and $false -- the names of FOOL term-level boolean constants are not quoted
 *
 * For interpreted symbols its legal to start with $
 *
 * It's legal for symbols to start with $$.
 *
 * @since 03/05/2013 train Manchester-London
 * @since 04/05/2015 Gothenburg -- do not quote FOOL true and false
 */
bool Signature::symbolNeedsQuoting(std::string name, bool interpreted, unsigned arity)
{
  ASS_G(name.length(),0);

  //we don't want to quote these type constructors, but we
  //also don't want them to be treated as interpreted symbols
  //hence the hack below, AYB
  if(name=="$int" || name=="$real" || name=="$rat" || 
     name=="$i" || name=="$o"){
    return false;
  }

  if (name=="=" || (interpreted && arity==0)) {
    return false;
  }

  const char* c = name.c_str();
  bool quote = false;
  bool first = true;
  if (*c=='$') {
    if (*(c+1)=='$') {
      c+=2; //skip the initial $$
      first = false;
    } else if (interpreted) {
      c++; //skip the initial $ for interpreted
      first = false;
    }
  }
  while(!quote && *c) {
    quote |= charNeedsQuoting(*c, first);
    first = false;
    c++;
  }
  if (!quote) { return false; }
  if (name=="$distinct") {
    //TODO: remove this once we properly support the $distinct predicate and quoting
    return false;
  }
  if (name.find("$array") == 0) {
    //TODO: a hacky solution not to quote array sorts
    return false;
  }
  return true;
} // Signature::symbolNeedsQuoting


TermAlgebraConstructor* Signature::getTermAlgebraConstructor(unsigned functor)
{
  if (getFunction(functor)->termAlgebraCons()) {
    TermAlgebra *ta = _termAlgebras.get(getFunction(functor)->fnType()->result().term()->functor());
    if (ta) {
      for (unsigned i = 0; i < ta->nConstructors(); i++) {
        TermAlgebraConstructor *c = ta->constructor(i);
        if (c->functor() == functor)
          return c;
      }
    }
  }

  return nullptr;
}

/**
 * Return true if the name containing che character must be quoted
 */
bool Signature::charNeedsQuoting(char c, bool first)
{
  switch (c) {
  case 'a':
  case 'b':
  case 'c':
  case 'd':
  case 'e':
  case 'f':
  case 'g':
  case 'h':
  case 'i':
  case 'j':
  case 'k':
  case 'l':
  case 'm':
  case 'n':
  case 'o':
  case 'p':
  case 'q':
  case 'r':
  case 's':
  case 't':
  case 'u':
  case 'v':
  case 'w':
  case 'x':
  case 'y':
  case 'z':
//  case '$':
    return false;
  case 'A':
  case 'B':
  case 'C':
  case 'D':
  case 'E':
  case 'F':
  case 'G':
  case 'H':
  case 'I':
  case 'J':
  case 'K':
  case 'L':
  case 'M':
  case 'N':
  case 'O':
  case 'P':
  case 'Q':
  case 'R':
  case 'S':
  case 'T':
  case 'U':
  case 'V':
  case 'W':
  case 'X':
  case 'Y':
  case 'Z':
  case '_':
  case '0':
  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9':
    return first;
  default:
    return true;
  }
}
