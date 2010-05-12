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

#include "../Forwards.hpp"

#include "../Debug/Assertion.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/Map.hpp"
#include "../Lib/DHMap.hpp"

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
  protected:
    /** print name */
    const string _name;
    /** arity */
    unsigned _arity : 26;
    /** the object is of type InterpretedSymbol */
    unsigned _interpreted : 1;
    /** clauses with only skipped symbols will not be output as symbol eliminating */
    unsigned _skip : 1;
    /** marks propositional predicate symbols that are to
        be used as names during consequence finding */
    unsigned _cfName : 1;
    /** marks propositional predicate symbols that are to
        be used as names for splitting without backtracking
        when BDDs are not used */
    unsigned _swbName : 1;
    /** used in coloured proofs and interpolation */
    unsigned _color : 2;
  public:
    /** standard constructor */
    Symbol(const string& nm,unsigned arity)
      : _name(nm),
	_arity(arity),
	_interpreted(0),
	_skip(0),
	_cfName(0),
	_swbName(0),
	_color(COLOR_TRANSPARENT)
    {}
    void addColor(Color color);
    /** mark the symbol as skip for the purpose of symbol elimination */
    void markSkip() { _skip=1; }
    /** mark the symbol as name for consequence finding */
    void markCFName() { ASS_EQ(arity(), 0); _cfName=1; }
    /** mark the symbol as name for splitting without backtracking */
    void markSWBName() { ASS_EQ(arity(), 0); _swbName=1; }
    /** return true iff symbol is marked as skip for the purpose of symbol elimination */
    bool skip() { return _skip; }
    /** return true iff the symbol is marked as name predicate
        for consequence finding */
    bool cfName() { return _cfName; }
    /** return true iff the symbol is marked as name predicate
        for splitting without backtracking */
    bool swbName() { return _swbName; }
    /** return the colour of the symbol */
    Color color() const { return static_cast<Color>(_color); }
    /** Return the arity of the symbol */
    inline unsigned arity() const { return _arity; }
    /** Return the name of the symbol */
    inline const string& name() const { return _name; }
    /** Return true iff the object is of type InterpretedSymbol */
    inline bool interpreted() const { return _interpreted; }

    CLASS_NAME("Signature::Symbol");
    USE_ALLOCATOR(Symbol);
  }; // class Symbol

  class InterpretedSymbol
  : public Symbol
  {
  public:
    enum Interpretation
    {
      //functions

      UNARY_MINUS,
      PLUS,
      MINUS,
      MULTIPLY,
      DIVIDE,
      /** The X?Y:Z ternary operator like in C++ */
      IF_THEN_ELSE,

      //predicates

      GREATER,
      GREATER_EQUAL,
      LESS,
      LESS_EQUAL
    };

    static unsigned getArity(Interpretation i);
    static bool isFunction(Interpretation i);
  protected:
    union {
      int _value;
      Interpretation _interp;
    };

  public:

    InterpretedSymbol(const string& nm, Interpretation interp)
    : Symbol(nm, getArity(interp)), _interp(interp)
    {
      CALL("InterpretedSymbol");

      _interpreted=true;
    }
    InterpretedSymbol(const string& nm,int value)
    : Symbol(nm, 0), _value(value)
    {
      CALL("InterpretedSymbol");

      _interpreted=true;
    }

    /** Return integer value of the interpreted constant */
    inline int getValue() const { ASS(interpreted()); ASS_EQ(arity(),0); return _value; }
    /** Return the interpreted function that corresponds to this symbol */
    inline Interpretation getInterpretation() const { ASS(interpreted()); ASS_NEQ(arity(),0); return _interp; }
  };

  typedef Map<string,unsigned,Hash> SymbolMap;

  void registerInterpretedFunction(const string& name,unsigned arity,
      InterpretedSymbol::Interpretation interpretation);
  void registerInterpretedPredicate(const string& name, unsigned arity,
      InterpretedSymbol::Interpretation interpretation);
  unsigned addInterpretedConstant(int value);

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
    return _funs[number]->name();
  }
  /** return the name of a predicate with a given number */
  const string& predicateName(int number)
  {
    return _preds[number]->name();
  }
  /** return the arity of a function with a given number */
  const unsigned functionArity(int number)
  {
    return _funs[number]->arity();
  }
  /** return the arity of a predicate with a given number */
  const unsigned predicateArity(int number)
  {
    return _preds[number]->arity();
  }

  const bool predicateColored(int number)
  {
    return _preds[number]->color()!=COLOR_TRANSPARENT;
  }

  const bool functionColored(int number)
  {
    return _funs[number]->color()!=COLOR_TRANSPARENT;
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

  /** Return the function symbol by its number */
  inline Symbol* getFunction(unsigned n)
  {
    ASS(n < _funs.length());
    return _funs[n];
  } // getFunction
  /** Return the predicate symbol by its number */
  inline Symbol* getPredicate(unsigned n)
  {
    ASS(n < _preds.length());
    return _preds[n];
  } // getPredicate

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
  /** Map for the arity_check options: maps symbols to their arities */
  SymbolMap _arityCheck;
  /** Last number used for name predicates */
  int _lastName;
  /** Last number used for skolem functions */
  int _lastSkolem;

  /** Map from integers to constant symbols representing them */
  DHMap<int, unsigned> _intConstants;

  static string key(const string& name,int arity);
}; // class Signature

}

#endif // __Signature__
