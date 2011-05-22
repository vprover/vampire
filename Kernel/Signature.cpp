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
Signature::Symbol::Symbol(const string& nm,unsigned arity, bool interpreted)
  : _name(nm),
    _arity(arity),
    _interpreted(interpreted ? 1 : 0),
    _skip(0),
    _cfName(0),
    _swbName(0),
    _color(COLOR_TRANSPARENT),
    _stringConstant(0),
    _type(0),
    _distinctGroups(0)
{

  //handle quoting
  const char* c=_name.c_str();
  //we do not put quotation marks around equality, although it is not an
  //atomic_word (in the sense of the TPTP syntax)
  //Also numbers are not quoted. However names that just look like numbers
  //(the distinction here is that they are not interpreted) are quoted.
  if((!interpreted || (_name!="=" && arity!=0)) && *c) {
    bool quote=needsQuoting(*c, true);
    c++;
    while(*c) {
      if(needsQuoting(*c, false)) {
	quote=true;
	break;
      }
      c++;
    }
    if(quote) {
      _name="'"+_name+"'";
    }
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
    _lastName(0),
    _lastIntroducedFunctionNumber(0),
    _lastSG(0)
{
  CALL("Signature::Signature");

  // initialize equality
  registerInterpretedPredicate("=", Theory::EQUAL);
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
 * Marks a function as interpreted.
 *
 * Must be called before the function appears in the problem for the first time.
 */
void Signature::registerInterpretedFunction(const string& name, Interpretation interpretation)
{
  CALL("Signature::registerInterpretedFunction");
  ASS(Theory::isFunction(interpretation));
  
  unsigned arity = Theory::getArity(interpretation);

  string symbolKey = key(name,arity);

  if (_funNames.find(symbolKey)) {
    ASSERTION_VIOLATION;
    USER_ERROR("Interpreted function '"+name+"' must be declared before it is used for the first time");
  }

  unsigned fnNum = _funs.length();
  _funs.push(new InterpretedSymbol(name, interpretation));
  _funNames.insert(symbolKey, fnNum);
  if(!_iSymbols.insert(interpretation, fnNum)) {
    USER_ERROR("One theory function cannot correspond to multiple signature functions: "+
	functionName(_iSymbols.get(interpretation))+", "+name);
  }
}

/**
 * Marks a predicate as interpreted.
 *
 * Must be called before the predicate appears in the problem for the first time.
 */
void Signature::registerInterpretedPredicate(const string& name, Interpretation interpretation)
{
  CALL("Signature::registerInterpretedPredicate");
  ASS(!Theory::isFunction(interpretation));

  unsigned arity = Theory::getArity(interpretation);

  string symbolKey = key(name,arity);

  if (_predNames.find(symbolKey)) {
    USER_ERROR("Interpreted predicate '"+name+"' must be declared before it is used for the first time");
  }

  unsigned predNum = _preds.length();
  _preds.push(new InterpretedSymbol(name,interpretation));
  _predNames.insert(symbolKey,predNum);
  if(!_iSymbols.insert(interpretation, predNum)) {
    USER_ERROR("One theory predicate cannot correspond to multiple signature predicates: "+
	predicateName(_iSymbols.get(interpretation))+", "+name);
  }
}

unsigned Signature::addIntegerConstant(const string& number)
{
  CALL("Signature::addIntegerConstant");

  string key = number + "_n";
  unsigned result;
  if(_funNames.find(key, result)) {
    return result;
  }
  result = _funs.length();
  _funs.push(new IntegerSymbol(number));
  return result;
}

unsigned Signature::addRationalConstant(const string& numerator, const string& denominator)
{
  CALL("Signature::addRationalConstant");

  RationalConstantType value(numerator, denominator);

  //we need to use the value to compute the key because we need to use
  //th rational number in the cannonical form
  string key = value.toString() + "_q";
  unsigned result;
  if(_funNames.find(key, result)) {
    return result;
  }
  result = _funs.length();
  _funs.push(new RationalSymbol(value));
  return result;
}

unsigned Signature::addRealConstant(const string& number)
{
  CALL("Signature::addRealConstant");

  RealConstantType value(number);

  //we need to use the value to compute the key because we need to use
  //the real number in the cannonical form
  string key = value.toString() + "_r";
  unsigned result;
  if(_funNames.find(key, result)) {
    return result;
  }
  result = _funs.length();
  _funs.push(new RealSymbol(value));
  return result;
}

/**
 * If an interpreted constant of given value exists, return its
 * number. Otherwise add a new one and return its number.
 */
unsigned Signature::addInterpretedConstant(InterpretedType value)
{
  CALL("Signature::addInterpretedConstant");

  unsigned result;
  if(_iConstants.find(value, result)) {
    return result;
  }

  string name=Int::toString(value);
//  string name= (value>=0) ? Int::toString(value) : ("uminus("+Int::toString(abs(value))+")");

  //we do not insert the constant into the _funNames map, as we will always
  //access them through the _iConstants map. There cannot be a name clash as
  //non-interpreted constants that appear like numbers must be in quotation
  //marks ('1' instead of 1 -- the later is a number)

  string symbolKey = key(name,0);
  //all integer constants must be registered in _iConstants

  result = _funs.length();
  _funs.push(new InterpretedSymbol(name,value));
  _iConstants.insert(value, result);
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
  case Theory::SUCCESSOR:
    name="++";
    break;
  case Theory::UNARY_MINUS:
    name="-";
    break;
  case Theory::PLUS:
    name="+";
    break;
  case Theory::MINUS:
    name="-";
    break;
  case Theory::MULTIPLY:
    name="*";
    break;
  case Theory::DIVIDE:
    name="$div";
    break;
  case Theory::INT_DIVIDE:
    name="/";
    break;
  case Theory::GREATER:
    name="$greater";
    break;
  case Theory::GREATER_EQUAL:
    name="$geq";
    break;
  case Theory::LESS:
    name="$less";
    break;
  case Theory::LESS_EQUAL:
    name="$leq";
  case Theory::INT_GREATER:
    name=">";
    break;
  case Theory::INT_GREATER_EQUAL:
    name=">=";
    break;
  case Theory::INT_LESS:
    name="<";
    break;
  case Theory::INT_LESS_EQUAL:
    name="<=";
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
    registerInterpretedFunction(name, interp);
  }
  else {
    if(predicateExists(name, arity)) {
      int i=0;
      while(predicateExists(name+Int::toString(i), arity)) {
        i++;
      }
      name=name+Int::toString(i);
    }
    registerInterpretedPredicate(name, interp);
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

  result = _funs.length();
  Symbol* sym = new Symbol(name,0);
  sym->markStringConstant();
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
 *
 * @since 01/07/2005 Manchester
 */
unsigned Signature::addNamePredicate (unsigned arity, const char* suffix)
{
  CALL("Signature::addNamePredicate");

  string suffixStr = suffix ? ("_" + string(suffix)) : "";
  string prefix("sP");
  prefix+=env.options->namePrefix();
  for (;;) {
    string name = prefix + Int::toString(_lastName++) + suffixStr;
    bool added;
    unsigned result = addPredicate(name,arity,added);
    if (added) {
      return result;
    }
  }
} // addNamePredicate

unsigned Signature::addIntroducedFunction(unsigned arity, const char* prefix0, const char* suffix)
{
  CALL("Signature::addIntroducedFunction");

  string prefix(prefix0);
  prefix+=env.options->namePrefix();
  for (;;) {
    string name = prefix + Int::toString(_lastIntroducedFunctionNumber++);
    if(suffix) {
      name=name+"_"+suffix;
    }
    bool added;
    unsigned result = addFunction(name,arity,added);
    if (added) {
      getFunction(result)->markSkip();
      return result;
    }
  }
}

/**
 * Return a new Skolem function. If @b suffix is nonzero, include it
 * into the name of the Skolem function.
 * @since 01/07/2005 Manchester
 */
unsigned Signature::addSkolemFunction (unsigned arity, const char* suffix)
{
  CALL("Signature::addSkolemFunction");

  return addIntroducedFunction(arity, "sK", suffix);
} // addSkolemFunction

/**
 * Return number of a new function to be used in if-then-else elimination
 */
unsigned Signature::addIteFunction(unsigned arity)
{
  CALL("Signature::addIteFunction");

  return addIntroducedFunction(arity, "sG");
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

/**
 * Return true if the name containing che character must be quoted
 */
bool Signature::needsQuoting(char c, bool first)
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
