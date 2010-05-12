/**
 * @file Signature.cpp
 * Implements class Signature consisting of predicate and function symbols
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Int.hpp"
#include "../Shell/Options.hpp"
#include "Signature.hpp"

using namespace std;
using namespace Kernel;

/**
 * Return arity of the symbol that is interpreted by Interpretation
 * @b i.
 */
unsigned Signature::InterpretedSymbol::getArity(Interpretation i)
{
  CALL("Signature::InterpretedSymbol::getArity");

  switch(i) {
  case UNARY_MINUS:
    return 1;

  case PLUS:
  case MINUS:
  case MULTIPLY:
  case DIVIDE:
  case GREATER:
  case GREATER_EQUAL:
  case LESS:
  case LESS_EQUAL:
    return 2;

  case IF_THEN_ELSE:
    return 3;
  }
  ASSERTION_VIOLATION;
}

/**
 * Create a Signature.
 * @since 07/05/2007 Manchester
 */
Signature::Signature ()
  : _funs(32),
    _preds(32),
    _lastName(0),
    _lastSkolem(0)
{
  CALL("Signature::Signature");

  // initialize equality
  addPredicate("=", 2);
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

  string prefix("$n");
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

/**
 * Return a new Skolem function
 * @since 01/07/2005 Manchester
 */
unsigned Signature::addSkolemFunction (unsigned arity)
{
  CALL("Signature::addSkolemFunction");

  string prefix("$sk");
  prefix+=env.options->namePrefix();
  for (;;) {
    string name = prefix + Int::toString(_lastSkolem++);
    bool added;
    unsigned result = addFunction(name,arity,added);
    if (added) {
      getFunction(result)->markSkip();
      return result;
    }
  }
} // addSkolemFunction

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

