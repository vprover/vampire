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

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Map.hpp"
#include "Lib/DHMap.hpp"

#include "Sorts.hpp"
#include "Theory.hpp"

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
    string _name;
    /** arity */
    unsigned _arity : 23;
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
    /** marks predicates that are equality proxy */
    unsigned _equalityProxy : 1;
    /** used in coloured proofs and interpolation */
    unsigned _color : 2;
    /** marks distinct string constants */
    unsigned _stringConstant : 1;
    /** predicate introduced for query answering */
    unsigned _answerPredicate : 1;
    /** Either a FunctionType of a PredicateType object */
    mutable BaseType* _type;
    /** List of distinct groups the constant is a member of */
    List<unsigned>* _distinctGroups;

    ~Symbol();
  public:
    /** standard constructor */
    Symbol(const string& nm,unsigned arity, bool interpreted=false, bool stringConstant=false);
    void destroyFnSymbol();
    void destroyPredSymbol();

    void addColor(Color color);
    /** mark the symbol as skip for the purpose of symbol elimination */
    void markSkip() { _skip=1; }
    /** mark the symbol as name for consequence finding */
    void markCFName() { ASS_EQ(arity(), 0); _cfName=1; }
    /** mark the symbol as name for splitting without backtracking */
    void markSWBName() { ASS_EQ(arity(), 0); _swbName=1; }
    /** mark symbol to be an answer predicate */
    void markAnswerPredicate() { _answerPredicate=1; }
    /** mark predicate to be an equality proxy */
    void markEqualityProxy() { _equalityProxy=1; }
    /** return true iff symbol is marked as skip for the purpose of symbol elimination */
    bool skip() const { return _skip; }
    /** return true iff the symbol is marked as name predicate
        for consequence finding */
    bool cfName() const { return _cfName; }
    /** return true iff the symbol is marked as name predicate
        for splitting without backtracking */
    bool swbName() const { return _swbName; }
    /** return the colour of the symbol */
    Color color() const { return static_cast<Color>(_color); }
    /** Return the arity of the symbol */
    inline unsigned arity() const { return _arity; }
    /** Return the name of the symbol */
    inline const string& name() const { return _name; }
    /** Return true iff the object is of type InterpretedSymbol */
    inline bool interpreted() const { return _interpreted; }
    /** Return true iff symbol is a distinct string constant */
    inline bool stringConstant() const { return _stringConstant; }
    /** Return true iff symbol is an answer predicate */
    inline bool answerPredicate() const { return _answerPredicate; }
    /** Return true iff symbol is an equality proxy */
    inline bool equalityProxy() const { return _equalityProxy; }

    /** Return true if symbol is an integer constant */
    inline bool integerConstant() const
    { return interpreted() && arity()==0 && fnType()->result()==Sorts::SRT_INTEGER; }
    /** Return true if symbol is a rational constant */
    inline bool rationalConstant() const
    { return interpreted() && arity()==0 && fnType()->result()==Sorts::SRT_RATIONAL; }
    /** Return true if symbol is a real constant */
    inline bool realConstant() const
    { return interpreted() && arity()==0 && fnType()->result()==Sorts::SRT_REAL; }

    /** Return value of an integer constant */
    inline IntegerConstantType integerValue() const
    { ASS(integerConstant()); return static_cast<const IntegerSymbol*>(this)->_intValue; }
    /** Return value of a rational constant */
    inline RationalConstantType rationalValue() const
    { ASS(rationalConstant()); return static_cast<const RationalSymbol*>(this)->_ratValue; }
    /** Return value of a real constant */
    inline RealConstantType realValue() const
    { ASS(realConstant()); return static_cast<const RealSymbol*>(this)->_realValue; }

    const List<unsigned>* distinctGroups() const { return _distinctGroups; }
    void addToDistinctGroup(unsigned group);

    void setType(BaseType* type);
    FunctionType* fnType() const;
    PredicateType* predType() const;

    CLASS_NAME("Signature::Symbol");
    USE_ALLOCATOR(Symbol);
  }; // class Symbol

  class InterpretedSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    Interpretation _interp;

  public:

    InterpretedSymbol(const string& nm, Interpretation interp)
    : Symbol(nm, Theory::getArity(interp), true), _interp(interp)
    {
      CALL("InterpretedSymbol");
    }

    InterpretedSymbol(const string& nm)
    : Symbol(nm, 0, true)
    {
      CALL("InterpretedSymbol");
    }
    CLASS_NAME("Signature::InterpretedSymbol");
    USE_ALLOCATOR(InterpretedSymbol);

    /** Return the interpreted function that corresponds to this symbol */
    inline Interpretation getInterpretation() const { ASS(interpreted()); ASS_NEQ(arity(),0); return _interp; }
  };

  class IntegerSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    IntegerConstantType _intValue;

  public:
    IntegerSymbol(const IntegerConstantType& val)
    : Symbol(val.toString(), 0, true), _intValue(val)
    {
      CALL("IntegerSymbol");

      setType(new FunctionType(0, 0, Sorts::SRT_INTEGER));
      addToDistinctGroup(INTEGER_DISTINCT_GROUP);
    }
    CLASS_NAME("Signature::IntegerSymbol");
    USE_ALLOCATOR(IntegerSymbol);
  };

  class RationalSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    RationalConstantType _ratValue;

  public:
    RationalSymbol(const RationalConstantType& val)
    : Symbol(val.toString(), 0, true), _ratValue(val)
    {
      CALL("RationalSymbol");

      setType(new FunctionType(0, 0, Sorts::SRT_RATIONAL));
      addToDistinctGroup(RATIONAL_DISTINCT_GROUP);
    }
    CLASS_NAME("Signature::RationalSymbol");
    USE_ALLOCATOR(RationalSymbol);
  };

  class RealSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    RealConstantType _realValue;

  public:
    RealSymbol(const RealConstantType& val)
    : Symbol(val.toString(), 0, true), _realValue(val)
    {
      CALL("RealSymbol");

      setType(new FunctionType(0, 0, Sorts::SRT_REAL));
      addToDistinctGroup(REAL_DISTINCT_GROUP);
    }
    CLASS_NAME("Signature::RealSymbol");
    USE_ALLOCATOR(RealSymbol);
  };

  unsigned addInterpretedFunction(Interpretation itp, const string& name);
  unsigned addInterpretedPredicate(Interpretation itp, const string& name);


  unsigned addIntegerConstant(const string& number);
  unsigned addRationalConstant(const string& numerator, const string& denominator);
  unsigned addRealConstant(const string& number);

  unsigned addIntegerConstant(const IntegerConstantType& number);
  unsigned addRationalConstant(const RationalConstantType& number);
  unsigned addRealConstant(const RealConstantType& number);

  unsigned getInterpretingSymbol(Interpretation interp);

  /** Return true iff there is a symbol interpreted by Interpretation @b interp */
  bool haveInterpretingSymbol(Interpretation interp) const { return _iSymbols.find(interp); }

  /**
   * Return true iff we have any declared interpreted symbols
   *
   * The equality symbol is always present and is interpreted,
   * so we return true only if we have any other interpreted
   * symbols.
   */
  bool anyInterpretedSymbols() const
  {
    CALL("Signature::anyInterpretedSymbols");
    ASS_G(_iSymbols.size(),0); //we always have equality which is interpreted

    return _iSymbols.size()!=1;
  }

  unsigned addFreshFunction(unsigned arity, const char* prefix, const char* suffix = 0);
  unsigned addIteFunction(unsigned arity);
  unsigned addSkolemFunction(unsigned arity,const char* suffix = 0);

  unsigned addFreshPredicate(unsigned arity, const char* prefix, const char* suffix = 0);
  unsigned addNamePredicate(unsigned arity);

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
  /**
   * If a unique string constant with this name and arity exists, return its number.
   * Otherwise, add a new one and return its number.
   *
   * The added constant is of sort Sorts::SRT_DEFAULT.
   */
  unsigned addStringConstant(const string& name);

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
    CALL("Signature::functionArity");
    return _funs[number]->arity();
  }
  /** return the arity of a predicate with a given number */
  const unsigned predicateArity(int number)
  {
    CALL("Signature::predicateArity");
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

  bool functionExists(const string& name,unsigned arity) const;
  bool predicateExists(const string& name,unsigned arity) const;

  Unit* getDistinctGroupPremise(unsigned group);
  unsigned createDistinctGroup(Unit* premise = 0);
  void addToDistinctGroup(unsigned constantSymbol, unsigned groupId);

  static string key(const string& name,int arity);

  /** the number of string constants */
  bool strings() const {return _strings;}
  /** the number of integer constants */
  bool integers() const {return _integers;}
  /** the number of rational constants */
  bool rationals() const {return _rationals;}
  /** the number of real constants */
  bool reals() const {return _reals;}
private:

  static const unsigned STRING_DISTINCT_GROUP;
  static const unsigned INTEGER_DISTINCT_GROUP;
  static const unsigned RATIONAL_DISTINCT_GROUP;
  static const unsigned REAL_DISTINCT_GROUP;

  static bool symbolNeedsQuoting(string name, bool interpreted, unsigned arity, bool stringConstant);
  static bool charNeedsQuoting(char c, bool first);

  /** Stack of function symbols */
  Stack<Symbol*> _funs;
  /** Stack of predicate symbols */
  Stack<Symbol*> _preds;
  /**
   * Map from string "name_arity" to their numbers
   *
   * String constants have key "value_c", integer constants "value_n",
   * rational "numerator_denominator_q" and real "value_r".
   */
  SymbolMap _funNames;
  /** Map from string "name_arity" to their numbers */
  SymbolMap _predNames;
  /** Map for the arity_check options: maps symbols to their arities */
  SymbolMap _arityCheck;
  /** Last number used for fresh functions and predicates */
  int _nextFreshSymbolNumber;

  Stack<Unit*> _distinctGroupPremises;

  /**
   * Map from Interpretation values to function and predicate symbols representing them
   *
   * We mix here function and predicate symbols, but it is not a problem, as
   * the Interpretation value already determines whether we deal with a function
   * or a predicate.
   */
  DHMap<Interpretation, unsigned> _iSymbols;
  /** the number of string constants */
  bool _strings;
  /** the number of integer constants */
  bool _integers;
  /** the number of rational constants */
  bool _rationals;
  /** the number of real constants */
  bool _reals;
}; // class Signature

}

#endif // __Signature__
