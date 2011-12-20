/**
 * @file Signature.cpp
 * Implements class Signature consisting of predicate and function symbols
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Shell/Options.hpp"
#include "Signature.hpp"

using namespace std;
using namespace Kernel;

const unsigned Signature::STRING_DISTINCT_GROUP = 0;
const unsigned Signature::INTEGER_DISTINCT_GROUP = 1;
const unsigned Signature::RATIONAL_DISTINCT_GROUP = 2;
const unsigned Signature::REAL_DISTINCT_GROUP = 3;

/** standard constructor */
Signature::Symbol::Symbol(const string& nm,unsigned arity, bool interpreted, bool stringConstant)
  : _name(nm),
    _arity(arity),
    _interpreted(interpreted ? 1 : 0),
    _introduced(0),
    _protected(0),
    _skip(0),
    _cfName(0),
    _swbName(0),
    _equalityProxy(0),
    _color(COLOR_TRANSPARENT),
    _stringConstant(stringConstant ? 1: 0),
    _answerPredicate(0),
    _type(0),
    _distinctGroups(0)
{
  CALL("Signature::Symbol::Symbol");
  ASS(!stringConstant || arity==0);

  if(symbolNeedsQuoting(_name, interpreted, arity, stringConstant)) {
    _name="'"+_name+"'";
  }
  if(_interpreted || isProtectedName(nm)) {
    markProtected();
  }
}

Signature::Symbol::~Symbol()
{
  CALL("Signature::Symbol::~Symbol");

  if(_type) {
    delete _type;
  }
}

/**
 * Deallocate function Symbol object
 */
void Signature::Symbol::destroyFnSymbol()
{
  CALL("Signature::Symbol::destroyFnSymbol");

  if(integerConstant()) {
    delete static_cast<IntegerSymbol*>(this);
  }
  else if(rationalConstant()) {
    delete static_cast<RationalSymbol*>(this);
  }
  else if(realConstant()) {
    delete static_cast<RealSymbol*>(this);
  }
  else if(interpreted()) {
    delete static_cast<InterpretedSymbol*>(this);
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
  CALL("Signature::Symbol::destroyPredSymbol");

  if(interpreted()) {
    delete static_cast<InterpretedSymbol*>(this);
  }
  else {
    delete this;
  }
}

/**
 * Add constant symbol into a distinct group
 *
 * A constant can be added into one particular distinct group
 * at most once
 */
void Signature::Symbol::addToDistinctGroup(unsigned group)
{
  CALL("Signature::Symbol::addToDistinctGroup");

  ASS_EQ(arity(), 0);
  ASS(!_distinctGroups->member(group))

  List<unsigned>::push(group, _distinctGroups);
}

/**
 * Set type of the symbol
 *
 * The type can be set only once for each symbol, and if the type
 * should be different from the default type, this function must be
 * called before any call to @c fnType() or @c predType().
 */
void Signature::Symbol::setType(BaseType* type)
{
  CALL("Signature::Symbol::setType");
  ASS(!_type);

  _type = type;
}

/**
 * Return the type of a function symbol
 *
 * If the @c setType() function was not called before, the function
 * symbol is assigned a default type.
 */
FunctionType* Signature::Symbol::fnType() const
{
  CALL("Signature::Symbol::fnType");

  if(!_type) {
    _type = new FunctionType(arity());
  }
  return static_cast<FunctionType*>(_type);
}

/**
 * Return the type of a predicate symbol
 *
 * If the @c setType() function was not called before, the function
 * symbol is assigned a default type.
 */
PredicateType* Signature::Symbol::predType() const
{
  CALL("Signature::Symbol::predType");

  if(!_type) {
    _type = new PredicateType(arity());
  }
  return static_cast<PredicateType*>(_type);
}


/**
 * Create a Signature.
 * @since 07/05/2007 Manchester
 */
Signature::Signature ()
  : _funs(32),
    _preds(32),
    _nextFreshSymbolNumber(0),
    _strings(0),
    _integers(0),
    _rationals(0),
    _reals(0)
{
  CALL("Signature::Signature");

  // initialize equality
  addInterpretedPredicate(Theory::EQUAL, "=");
  ASS_EQ(predicateName(0), "="); //equality must have number 0
  getPredicate(0)->markSkip();

  unsigned aux;
  aux = createDistinctGroup();
  ASS_EQ(STRING_DISTINCT_GROUP, aux);
  aux = createDistinctGroup();
  ASS_EQ(INTEGER_DISTINCT_GROUP, aux);
  aux = createDistinctGroup();
  ASS_EQ(RATIONAL_DISTINCT_GROUP, aux);
  aux = createDistinctGroup();
  ASS_EQ(REAL_DISTINCT_GROUP, aux);
} // Signature::Signature

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
} // Signature::~Signature

/**
 * Add interpreted function
 */
unsigned Signature::addInterpretedFunction(Interpretation interpretation, const string& name)
{
  CALL("Signature::addInterpretedFunction");
  ASS(Theory::isFunction(interpretation));

  unsigned res;
  if(_iSymbols.find(interpretation,res)) { // already declared
    if(name!=functionName(res)) {
      USER_ERROR("Interpreted function '"+functionName(res)+"' has the same interpretation as '"+name+"' should have");
    }
    return res;
  }

  string symbolKey = name+"_i"+Int::toString(interpretation);

  ASS(!_funNames.find(symbolKey));

  unsigned fnNum = _funs.length();
  InterpretedSymbol* sym = new InterpretedSymbol(name, interpretation);
  _funs.push(sym);
  _funNames.insert(symbolKey, fnNum);
  ALWAYS(_iSymbols.insert(interpretation, fnNum));
  BaseType* fnType = Theory::getOperationType(interpretation);
  ASS(fnType->isFunctionType());
  sym->setType(fnType);

  return fnNum;
}

/**
 * Add interpreted predicate
 */
unsigned Signature::addInterpretedPredicate(Interpretation interpretation, const string& name)
{
  CALL("Signature::addInterpretedPredicate");
  ASS(!Theory::isFunction(interpretation));

  unsigned res;
  if(_iSymbols.find(interpretation,res)) { // already declared
    if(name!=predicateName(res)) {
      USER_ERROR("Interpreted predicate '"+predicateName(res)+"' has the same interpretation as '"+name+"' should have");
    }
    return res;
  }

  string symbolKey = name+"_i"+Int::toString(interpretation);

  ASS(!_predNames.find(symbolKey));

  unsigned predNum = _preds.length();
  InterpretedSymbol* sym = new InterpretedSymbol(name, interpretation);
  _preds.push(sym);
  _predNames.insert(symbolKey,predNum);
  ALWAYS(_iSymbols.insert(interpretation, predNum));
  if(predNum!=0) {
    BaseType* predType = Theory::getOperationType(interpretation);
    ASS(!predType->isFunctionType());
    sym->setType(predType);
  }
  return predNum;
}



unsigned Signature::addIntegerConstant(const string& number)
{
  CALL("Signature::addIntegerConstant(string)");

  IntegerConstantType value(number);
  return addIntegerConstant(value);
}

unsigned Signature::addIntegerConstant(const IntegerConstantType& value)
{
  CALL("Signature::addIntegerConstant");

  //TODO: something smarter, so that we don't need to convert all values to string
  string key = value.toString() + "_n";
  unsigned result;
  if(_funNames.find(key, result)) {
    return result;
  }
  _integers++;
  result = _funs.length();
  _funs.push(new IntegerSymbol(value));
  _funNames.insert(key, result);
  return result;
}

unsigned Signature::addRationalConstant(const string& numerator, const string& denominator)
{
  CALL("Signature::addRationalConstant(string,string)");

  RationalConstantType value(numerator, denominator);
  return addRationalConstant(value);
}

unsigned Signature::addRationalConstant(const RationalConstantType& value)
{
  CALL("Signature::addRationalConstant");

  string key = value.toString() + "_q";
  unsigned result;
  if(_funNames.find(key, result)) {
    return result;
  }
  _rationals++;
  result = _funs.length();
  _funs.push(new RationalSymbol(value));
  _funNames.insert(key, result);
  return result;
}

unsigned Signature::addRealConstant(const string& number)
{
  CALL("Signature::addRealConstant(string)");

  RealConstantType value(number);
  return addRealConstant(value);
}

unsigned Signature::addRealConstant(const RealConstantType& value)
{
  CALL("Signature::addRealConstant");

  string key = value.toString() + "_r";
  unsigned result;
  if(_funNames.find(key, result)) {
    return result;
  }
  _reals++;
  result = _funs.length();
  _funs.push(new RealSymbol(value));
  _funNames.insert(key, result);
  return result;
}

/**
 * Return number of symbol that is interpreted by Interpretation @b interp.
 *
 * If no such symbol exists, it is created.
 */
unsigned Signature::getInterpretingSymbol(Interpretation interp)
{
  CALL("Signature::getInterpretingSymbol");

  unsigned res;
  if(_iSymbols.find(interp, res)) {
    return res;
  }
  string name;
  switch(interp) {
  case Theory::INT_SUCCESSOR:
    //this one is not according the TPTP arithmetic (it doesn't have successor)
    name="$successor";
    break;
  case Theory::INT_DIVIDE:
  case Theory::RAT_DIVIDE:
  case Theory::REAL_DIVIDE:
    //this one is not according the TPTP arithmetic (it doesn't have division)
    name="$divide";
    break;
  case Theory::INT_UNARY_MINUS:
  case Theory::RAT_UNARY_MINUS:
  case Theory::REAL_UNARY_MINUS:
    name="$uminus";
    break;
  case Theory::INT_PLUS:
  case Theory::RAT_PLUS:
  case Theory::REAL_PLUS:
    name="$sum";
    break;
  case Theory::INT_MINUS:
  case Theory::RAT_MINUS:
  case Theory::REAL_MINUS:
    name="$difference";
    break;
  case Theory::INT_MULTIPLY:
  case Theory::RAT_MULTIPLY:
  case Theory::REAL_MULTIPLY:
    name="$product";
    break;
  case Theory::INT_GREATER:
  case Theory::RAT_GREATER:
  case Theory::REAL_GREATER:
    name="$greater";
    break;
  case Theory::INT_GREATER_EQUAL:
  case Theory::RAT_GREATER_EQUAL:
  case Theory::REAL_GREATER_EQUAL:
    name="$greatereq";
    break;
  case Theory::INT_LESS:
  case Theory::RAT_LESS:
  case Theory::REAL_LESS:
    name="$less";
    break;
  case Theory::INT_LESS_EQUAL:
  case Theory::RAT_LESS_EQUAL:
  case Theory::REAL_LESS_EQUAL:
    name="$lesseq";
    break;
  case Theory::INT_IS_INT:
  case Theory::RAT_IS_INT:
  case Theory::REAL_IS_INT:
    name="$is_int";
    break;
  case Theory::INT_IS_RAT:
  case Theory::RAT_IS_RAT:
  case Theory::REAL_IS_RAT:
    name="$is_rat";
    break;
  case Theory::INT_IS_REAL:
  case Theory::RAT_IS_REAL:
  case Theory::REAL_IS_REAL:
    name="$is_real";
    break;
  case Theory::INT_TO_INT:
  case Theory::RAT_TO_INT:
  case Theory::REAL_TO_INT:
    name="$to_int";
    break;
  case Theory::INT_TO_RAT:
  case Theory::RAT_TO_RAT:
  case Theory::REAL_TO_RAT:
    name="$to_rat";
    break;
  case Theory::INT_TO_REAL:
  case Theory::RAT_TO_REAL:
  case Theory::REAL_TO_REAL:
    name="$to_real";
    break;
  default:
    ASSERTION_VIOLATION;
  }

  unsigned arity = Theory::getArity(interp);

  if(Theory::isFunction(interp)) {
    if(functionExists(name, arity)) {
      int i=0;
      while(functionExists(name+Int::toString(i), arity)) {
        i++;
      }
      name=name+Int::toString(i);
    }
    addInterpretedFunction(interp, name);
  }
  else {
    if(predicateExists(name, arity)) {
      int i=0;
      while(predicateExists(name+Int::toString(i), arity)) {
        i++;
      }
      name=name+Int::toString(i);
    }
    addInterpretedPredicate(interp, name);
  }

  //we have now registered a new function, so it should be present in the map
  return _iSymbols.get(interp);
}

/**
 * Return true if specified function exists
 */
bool Signature::functionExists(const string& name,unsigned arity) const
{
  CALL("Signature::functionExists");

  return _funNames.find(key(name, arity));
}

/**
 * Return true if specified predicate exists
 */
bool Signature::predicateExists(const string& name,unsigned arity) const
{
  CALL("Signature::predicateExists");

  return _predNames.find(key(name, arity));
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
unsigned Signature::addFunction (const string& name,
				 unsigned arity,
				 bool& added)
{
  CALL("Signature::addFunction");

  string symbolKey = key(name,arity);
#if VDEBUG
  unsigned result = 0;
#else
  unsigned result;
#endif
  if (_funNames.find(symbolKey,result)) {
    added = false;
    return result;
  }
  if (env.options->arityCheck()) {
    unsigned prev;
    if (_arityCheck.find(name,prev)) {
      unsigned prevArity = prev/2;
      bool isFun = prev % 2;
      USER_ERROR((string)"Symbol " + name +
		 " is used both as a function of arity " + Int::toString(arity) +
		 " and a " + (isFun ? "function" : "predicate") +
		 " of arity " + Int::toString(prevArity));
    }
    _arityCheck.insert(name,2*arity+1);
  }

  result = _funs.length();
  _funs.push(new Symbol(name,arity));
  _funNames.insert(symbolKey,result);
  added = true;
  return result;
} // Signature::addFunction

unsigned Signature::addStringConstant(const string& name)
{
  CALL("Signature::addStringConstant");

  string symbolKey = name + "_c";
#if VDEBUG
  unsigned result = 0;
#else
  unsigned result;
#endif
  if (_funNames.find(symbolKey,result)) {
    return result;
  }

  _strings++;
  string quotedName = "\"" + name + "\"";
  result = _funs.length();
  Symbol* sym = new Symbol(quotedName,0,false,true);
  sym->addToDistinctGroup(STRING_DISTINCT_GROUP);
  _funs.push(sym);
  _funNames.insert(symbolKey,result);
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
 */
unsigned Signature::addPredicate (const string& name,
				  unsigned arity,
				  bool& added)
{
  CALL("Signature::addPredicate");

  string symbolKey = key(name,arity);
#if VDEBUG
  unsigned result = 0;
#else
  unsigned result;
#endif
  if (_predNames.find(symbolKey,result)) {
    added = false;
    return result;
  }
  if (env.options->arityCheck()) {
    unsigned prev;
    if (_arityCheck.find(name,prev)) {
      unsigned prevArity = prev/2;
      bool isFun = prev % 2;
      USER_ERROR((string)"Symbol " + name +
		 " is used both as a predicate of arity " + Int::toString(arity) +
		 " and a " + (isFun ? "function" : "predicate") +
		 " of arity " + Int::toString(prevArity));
    }
    _arityCheck.insert(name,2*arity);
  }

  result = _preds.length();
  _preds.push(new Symbol(name,arity));
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
  CALL("Signature::addNamePredicate");
  return addFreshPredicate(arity,"sP");
} // addNamePredicate

/**
 * Add fresh function of a given arity and with a given prefix. If suffix is non-zero,
 * the function name will be prefixI, where I is an integer, otherwise it will be
 * prefixI_suffix. The new function will be marked as skip for the purpose of equality
 * elimination.
 */
unsigned Signature::addFreshFunction(unsigned arity, const char* prefix, const char* suffix)
{
  CALL("Signature::addFreshFunction");

  string pref(prefix);
  string suf(suffix ? string("_")+suffix : "");
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
 * Add fresh predicate of a given arity and with a given prefix. If suffix is non-zero,
 * the predicate name will be prefixI, where I is an integer, otherwise it will be
 * prefixI_suffix. The new predicate will be marked as skip for the purpose of equality
 * elimination.
 */
unsigned Signature::addFreshPredicate(unsigned arity, const char* prefix, const char* suffix)
{
  CALL("Signature::addFreshPredicate");

  string pref(prefix);
  string suf(suffix ? string("_")+suffix : "");
  bool added = false;
  unsigned result;
  //commented out because it could lead to introduction of function with the same name
  //that differ only in arity (which is OK with tptp, but iProver was complaining when
  //using Vampire as clausifier)
//  if(suffix) {
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
unsigned Signature::addSkolemFunction (unsigned arity, const char* suffix)
{
  CALL("Signature::addSkolemFunction");

  return addFreshFunction(arity, "sK", suffix);
} // addSkolemFunction

/**
 * Return number of a new function to be used in if-then-else elimination
 */
unsigned Signature::addIteFunction(unsigned arity)
{
  CALL("Signature::addIteFunction");

  return addFreshFunction(arity, "sG");
}

/**
 * Return the key "name_arity" used for hashing.
 * @since 27/02/2006 Redmond
 */
string Signature::key(const string& name,int arity)
{
  return name + '_' + Int::toString(arity);
} // Signature::key


/** Add a color to the symbol for interpolation and symbol elimination purposes */
void Signature::Symbol::addColor(Color color)
{
  ASS_L(color,3);
  ASS_G(color,0);
  ASS(env.colorUsed);

  if (_color && color != _color) {
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
  CALL("Signature::createDistinctGroup");

  unsigned res = _distinctGroupPremises.size();
  _distinctGroupPremises.push(premise);
  return res;
}

/**
 * Return premise of the distinct group, or 0 if the distinct group doesn't have any
 */
Unit* Signature::getDistinctGroupPremise(unsigned group)
{
  CALL("Signature::getDistinctGroupPremise");

  return _distinctGroupPremises[group];
}

/**
 * Add a constant into a group of distinct elements
 *
 * One constant can be added into one particular distinct group only once.
 */
void Signature::addToDistinctGroup(unsigned constantSymbol, unsigned groupId)
{
  CALL("Signature::addToDistinctGroup");

  Symbol* sym = getFunction(constantSymbol);
  sym->addToDistinctGroup(groupId);
}

bool Signature::isProtectedName(string name)
{
  CALL("Signature::isProtectedName");

  if(name=="$distinct") {
    //TODO: remove this hack once we properly support the $distinct predicate
    return true;
  }

  string protectedPrefix = env.options->protectedPrefix();
  if(protectedPrefix.size()==0) {
    return false;
  }
  if(name.substr(0, protectedPrefix.size())==protectedPrefix) {
    return true;
  }
  return false;
}

/**
 * Return true if specified symbol should be quoted
 *
 * The function charNeedsQuoting determines characters whose presence in
 * the symbol name implies that they should be quoted. There are however
 * several exceptions to it:
 *
 * Equality is not quoted
 *
 * String constants are not quoted (they are already in the double quotes)
 *
 * Numbers are not quoted. However names that just look like numbers
 * are quoted (the distinction is that these are not interpreted)
 *
 * $distinct predicate is not quoted
 *
 * For interpreted symbols its legal to start with $
 *
 * It's legal for symbols to start with $$
 */
bool Signature::symbolNeedsQuoting(string name, bool interpreted, unsigned arity, bool stringConstant)
{
  CALL("Signature::symbolNeedsQuoting");
  ASS_G(name.length(),0);

  if(stringConstant) { return false; }
  if(interpreted && (name=="=" || arity==0)) { return false; }

  const char* c = name.c_str();
  bool quote = false;
  bool first = true;
  if(*c=='$') {
    if(*(c+1)=='$') {
      c+=2; //skip the initial $$
      first = false;
    }
    else if(interpreted) {
      c++; //skip the initial $ for interpreted
      first = false;
    }
  }
  while(!quote && *c) {
    quote |= charNeedsQuoting(*c, first);
    first = false;
    c++;
  }
  if(!quote) { return false; }
  if(name=="$distinct") {
    //TODO: remove this once we properly support the $distinct predicate and quoting
    return false;
  }
  return true;
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
