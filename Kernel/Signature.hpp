/**
 * @file Signature.hpp
 * Defines class Signature consisting of predicate and function symbols
 *
 * @since 07/05/2007 Manchester, created anew instead of the old overcomplicated
 *        Signature
 */

#ifndef __Signature__
#define __Signature__

#include <string>

#include "../Lib/Allocator.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/Map.hpp"

using namespace std;
using namespace Lib;

namespace Kernel {

/**
 * Class representing signatures.
 */
class Signature
{
 public:
  /** Function or predicate symbol */
  class Symbol {
  public:
    /** print name */
    const string name;
    /** arity */
    unsigned arity;
    /** standard constructor */
    Symbol(const string& nm,int ar)
      : name(nm),
	arity(ar)
    {}
    CLASS_NAME("Signature::Symbol");
    USE_ALLOCATOR(Symbol);
  }; // class Symbol
  typedef Map<string,unsigned,Hash> SymbolMap;

  unsigned addSkolemFunction(unsigned arity);
  /**
   * If a predicate with this name and arity exists, return its number.
   * Otherwise, add a new one and return its number.
   *
   * @param name name of the symbol
   * @param arity arity of the symbol
   * @since 07/05/2007 Manchester
   */
  unsigned addPredicate(const string& name,unsigned arity)
  {
    bool added;
    return addPredicate(name,arity,added);
  }
  /**
   * If a function with this name and arity exists, return its number.
   * Otherwise, add a new one and return its number.
   *
   * @since 28/12/2007 Manchester
   */
  unsigned addFunction(const string& name,unsigned arity)
  {
    bool added;
    return addFunction(name,arity,added);
  }
  unsigned addNamePredicate(unsigned arity);

  /** return the name of a function with a given number */
  const string& functionName(int number)
  {
    return _funs[number]->name;
  }
  /** return the name of a predicate with a given number */
  const string& predicateName(int number)
  {
    return _preds[number]->name;
  }
  /** return the arity of a function with a given number */
  const unsigned functionArity(int number)
  {
    return _funs[number]->arity;
  }
  /** return the arity of a predicate with a given number */
  const unsigned predicateArity(int number)
  {
    return _preds[number]->arity;
  }

  /** return true iff predicate of given @b name and @b arity exists. */
  bool isPredicateName(string name, unsigned arity)
  {
    string symbolKey = key(name,arity);
    unsigned tmp;
    return _predNames.find(symbolKey,tmp);
  }

  /** return the number of functions */
  int functions() const { return _funs.length(); }
  /** return the number of predicates */
  int predicates() const { return _preds.length(); }

  Signature();
  ~Signature();

  CLASS_NAME("Signature");
  USE_ALLOCATOR(Signature);

  unsigned addPredicate(const string& name,unsigned arity,bool& added);
  unsigned addFunction(const string& name,unsigned arity,bool& added);
private:

  /** Stack of function symbols */
  Stack<Symbol*> _funs;
  /** Stack of predicate symbols */
  Stack<Symbol*> _preds;
  /** Map from string "name_arity" to their numbers */
  SymbolMap _funNames;
  /** Map from string "name_arity" to their numbers */
  SymbolMap _predNames;
  /** Last number used for name predicates */
  int _lastName;
  /** Last number used for skolem functions */
  int _lastSkolem;

  static string key(const string& name,int arity);
}; // class Signature

}

#endif // __Signature__
