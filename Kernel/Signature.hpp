/**
 * @file Signature.hpp
 * Defines class Signature for handling signatures
 *
 * @since 07/05/2007 Manchester, created anew instead of the old overcomplicated
 *        Signature
 */

#ifndef __Signature__
#define __Signature__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Map.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/VString.hpp"

#include "Sorts.hpp"
#include "Theory.hpp"


namespace Kernel {

using namespace std;
using namespace Lib;

/**
 * Class implementing signatures
 */
class Signature
{
 public:
  /** Function or predicate symbol */
  class Symbol {
  protected:
    /** print name */
    vstring _name;
    /** arity */
    unsigned _arity;
    /** the object is of type InterpretedSymbol */
    unsigned _interpreted : 1;
    /** symbol that doesn't come from input problem, but was introduced by Vampire */
    unsigned _introduced : 1;
    /** protected symbols aren't subject to any kind of preprocessing elimination */
    unsigned _protected : 1;
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
    /** marks numeric constants, they are only used in TPTP's fof declarations */
    unsigned _numericConstant : 1;
    /** predicate introduced for query answering */
    unsigned _answerPredicate : 1;
    /** Either a FunctionType of a PredicateType object */
    mutable BaseType* _type;
    /** List of distinct groups the constant is a member of, all members of a distinct group should be distinct from each other */
    List<unsigned>* _distinctGroups;

    ~Symbol();
  public:
    /** standard constructor */
    Symbol(const vstring& nm,unsigned arity, bool interpreted=false, bool stringConstant=false,bool numericConstant=false);
    void destroyFnSymbol();
    void destroyPredSymbol();

    void addColor(Color color);
    /** mark symbol that doesn't come from input problem, but was introduced by Vampire */
    void markIntroduced() { _introduced=1; }
    /** mark the symbol as protected so it is not being eliminated by preprocessing */
    void markProtected() { _protected=1; }
    /** mark the symbol as skip for the purpose of symbol elimination */
    void markSkip() { _skip=1; }
    /** mark the symbol as name for consequence finding */
    void markCFName() { ASS_EQ(arity(), 0); _cfName=1; markProtected(); }
    /** mark symbol to be an answer predicate */
    void markAnswerPredicate() { _answerPredicate=1; markProtected(); }
    /** mark the symbol as name for splitting without backtracking */
    void markSWBName() { ASS_EQ(arity(), 0); _swbName=1; }
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
    inline const vstring& name() const { return _name; }
    /** Return true iff the object is of type InterpretedSymbol */
    inline bool interpreted() const { return _interpreted; }
    /** Return true iff the symbol doesn't come from input problem but was introduced by Vampire */
    inline bool introduced() const { return _introduced; }
    /** Return true iff the symbol is must not be eliminated by proprocessing */
    inline bool protectedSymbol() const { return _protected; }
    /** Return true iff symbol is a distinct string constant */
    inline bool stringConstant() const { return _stringConstant; }
    /** Return true iff symbol is a numeric constant */
    inline bool numericConstant() const { return _numericConstant; }
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
    /** This takes the symbol number of this symbol as the symbol doesn't know it
        Note that this should only be called on a constant **/
    void addToDistinctGroup(unsigned group,unsigned this_number);

    void setType(BaseType* type);
    FunctionType* fnType() const;
    PredicateType* predType() const;

    CLASS_NAME(Signature::Symbol);
    USE_ALLOCATOR(Symbol);
  }; // class Symbol

  
  class VarSymbol{
  protected:
    /** print name*/
    vstring _name;
  public: 
    /**Standard Constructor*/
    VarSymbol(const vstring& nm);
    
    /** Return the name of the symbol*/
    inline const vstring& name() const {return _name;}
    
    CLASS_NAME("Signature::VarSymbol");
    USE_ALLOCATOR(VarSymbol);
  };//class VarSymbol
  
  
  class InterpretedSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    Interpretation _interp;

  public:

    InterpretedSymbol(const vstring& nm, Interpretation interp)
    : Symbol(nm, Theory::getArity(interp), true), _interp(interp)
    {
      CALL("InterpretedSymbol");
    }

    InterpretedSymbol(const vstring& nm)
    : Symbol(nm, 0, true)
    {
      CALL("InterpretedSymbol");
    }
    CLASS_NAME(Signature::InterpretedSymbol);
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
    }
    CLASS_NAME(Signature::IntegerSymbol);
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
    }
    CLASS_NAME(Signature::RationalSymbol);
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
    : Symbol(val.toNiceString(), 0, true), _realValue(val)
    {
      CALL("RealSymbol");

      setType(new FunctionType(0, 0, Sorts::SRT_REAL));
    }
    CLASS_NAME(Signature::RealSymbol);
    USE_ALLOCATOR(RealSymbol);
  };
    
  //////////////////////////////////////
  // Variable Symbol declarations
  //
  
  /**
   * If a variable with this name and arity exists, return its number 
   * Otherwise, add a new one and return its number 
   */
  unsigned addVar(const vstring& name){
    CALL("Signature::addVar");
    bool added;
    return addVar(name, added);
  }
  
  const vstring& varName(Var number){
    return _vars[number]->name();
  }
  
  /**return the number of variables */
  size_t vars() const {return _vars.length(); }
  
  
  /**return the function symbol by its number*/
  inline VarSymbol* getVar(unsigned n){
    CALL("Signature::getVar");
    ASS(n<vars());
    return _vars[n];
  }
  
  unsigned addVar(const vstring& name, bool& added);
  //////////////////////////////////////
  // Uninterpreted symbol declarations
  //

  unsigned addPredicate(const vstring& name,unsigned arity,bool& added);
  unsigned addFunction(const vstring& name,unsigned arity,bool& added);

  /**
   * If a predicate with this name and arity exists, return its number.
   * Otherwise, add a new one and return its number.
   *
   * @param name name of the symbol
   * @param arity arity of the symbol
   * @since 07/05/2007 Manchester
   */
  unsigned addPredicate(const vstring& name,unsigned arity)
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
  unsigned addFunction(const vstring& name,unsigned arity)
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
  unsigned addStringConstant(const vstring& name);
  unsigned addFreshFunction(unsigned arity, const char* prefix, const char* suffix = 0);
  unsigned addSkolemFunction(unsigned arity,const char* suffix = 0);
  unsigned addFreshPredicate(unsigned arity, const char* prefix, const char* suffix = 0);
  unsigned addNamePredicate(unsigned arity);

  // Interpreted symbol declarations

  unsigned addInterpretedFunction(Interpretation itp, const vstring& name);
  unsigned addInterpretedPredicate(Interpretation itp, const vstring& name);

  unsigned addIntegerConstant(const vstring& number,bool defaultSort);
  unsigned addRationalConstant(const vstring& numerator, const vstring& denominator,bool defaultSort);
  unsigned addRealConstant(const vstring& number,bool defaultSort);

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

  /** return the name of a function with a given number */
  const vstring& functionName(int number);
  /** return the name of a predicate with a given number */
  const vstring& predicateName(int number)
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
  bool isPredicateName(vstring name, unsigned arity)
  {
    vstring symbolKey = key(name,arity);
    unsigned tmp;
    return _predNames.find(symbolKey,tmp);
  }

  /** return the number of functions */
  unsigned functions() const { return _funs.length(); }
  /** return the number of predicates */
  unsigned predicates() const { return _preds.length(); }

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

  CLASS_NAME(Signature);
  USE_ALLOCATOR(Signature);

  bool functionExists(const vstring& name,unsigned arity) const;
  bool predicateExists(const vstring& name,unsigned arity) const;

  Unit* getDistinctGroupPremise(unsigned group);
  unsigned createDistinctGroup(Unit* premise = 0);
  void addToDistinctGroup(unsigned constantSymbol, unsigned groupId);
  bool hasDistinctGroups(){ return _distinctGroupsAddedTo; }
  void noDistinctGroupsLeft(){ _distinctGroupsAddedTo=false; }
  Stack<Stack<unsigned>*> getDistinctGroupMembers(){ return _distinctGroupMembers; }

  static vstring key(const vstring& name,int arity);

  /** the number of string constants */
  unsigned strings() const {return _strings;}
  /** the number of integer constants */
  unsigned integers() const {return _integers;}
  /** the number of rational constants */
  unsigned rationals() const {return _rationals;}
  /** the number of real constants */
  unsigned reals() const {return _reals;}

  static const unsigned STRING_DISTINCT_GROUP;
  static const unsigned INTEGER_DISTINCT_GROUP;
  static const unsigned RATIONAL_DISTINCT_GROUP;
  static const unsigned REAL_DISTINCT_GROUP;
  static const unsigned LAST_BUILT_IN_DISTINCT_GROUP;

  static const unsigned FOOL_FALSE;
  static const unsigned FOOL_TRUE;

private:
  static bool isProtectedName(vstring name);
  static bool symbolNeedsQuoting(vstring name, bool interpreted, unsigned arity);
  static bool charNeedsQuoting(char c, bool first);
  /** Stack of function symbols -- used for bound propagation*/
  Stack<VarSymbol*> _vars;
  /** Stack of function symbols */
  Stack<Symbol*> _funs;
  /** Stack of predicate symbols */
  Stack<Symbol*> _preds;
  /**
   * Map from vstring "name_arity" to their numbers
   *
   * String constants have key "value_c", integer constants "value_n",
   * rational "numerator_denominator_q" and real "value_r".
   */
  SymbolMap _funNames;
  /** Map from vstring "name_arity" to their numbers */
  SymbolMap _predNames;
  /** Map for the arity_check options: maps symbols to their arities */
  SymbolMap _arityCheck;
  /** Last number used for fresh functions and predicates */
  int _nextFreshSymbolNumber;

  /** Number of Skolem functions (this is just for LaTeX output) */
  unsigned _skolemFunctionCount;

  /** Map from symbol names to variable numbers*/
  SymbolMap _varNames;
  
  // Store the premise of a distinct group for proof printing, if 0 then group is input
  Stack<Unit*> _distinctGroupPremises;
  // We only store members up until a hard-coded limit i.e. the limit at which we will expand the group
  Stack<Stack<unsigned>*> _distinctGroupMembers;
  // Flag to indicate if any distinct groups have members
  bool _distinctGroupsAddedTo;

  /**
   * Map from Interpretation values to function and predicate symbols representing them
   *
   * We mix here function and predicate symbols, but it is not a problem, as
   * the Interpretation value already determines whether we deal with a function
   * or a predicate.
   */
  DHMap<Interpretation, unsigned> _iSymbols;
  /** the number of string constants */
  unsigned _strings;
  /** the number of integer constants */
  unsigned _integers;
  /** the number of rational constants */
  unsigned _rationals;
  /** the number of real constants */
  unsigned _reals;
}; // class Signature

}

#endif // __Signature__
