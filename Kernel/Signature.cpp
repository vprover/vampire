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

/** standard constructor */
Signature::Symbol::Symbol(const string& nm,unsigned arity, bool interpreted)
  : _name(nm),
    _arity(arity),
    _interpreted(interpreted ? 1 : 0),
    _skip(0),
    _cfName(0),
    _swbName(0),
    _color(COLOR_TRANSPARENT)
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
} // Signature::Signature

/**
 * Destroy a Signature.
 * @since 07/05/2007 Manchester
 */
Signature::~Signature ()
{
  for (int i = _funs.length()-1;i >= 0;i--) {
    delete _funs[i];
  }
  for (int i = _preds.length()-1;i >= 0;i--) {
    delete _preds[i];
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
unsigned Signature::addNamePredicate (unsigned arity)
{
  CALL("Signature::addNamePredicate");

  string prefix("sP");
  prefix+=env.options->namePrefix();
  for (;;) {
    string name = prefix + Int::toString(_lastName++);
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
