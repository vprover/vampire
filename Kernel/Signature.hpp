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

#include "Lib/Stack.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Map.hpp"
#include "Lib/List.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/SmartPtr.hpp"

#include "Shell/TermAlgebra.hpp"
#include "Shell/Options.hpp"

#include "OperatorType.hpp"
#include "Theory.hpp"

#include <climits>

namespace Kernel {

using namespace Lib;

/**
 * Class implementing signatures
 */
class Signature
{
  using SymbolKey = Coproduct<
      std::pair<std::string, unsigned> // <- (name, arity)
    , std::string // <- string-constant
    // (number, arity). 
    // if arity = 0 we mean a numeral constant
    // if arity = 1 we mean a linear multiplication
    , std::pair<IntegerConstantType, unsigned> 
    , std::pair<RationalConstantType, unsigned> 
    , std::pair<RealConstantType, unsigned> 
    , std::pair<Theory::Interpretation, OperatorType*>
    >;

  using SymbolMap = Map<SymbolKey, unsigned>;
 public:
  /** Function or predicate symbol */
  
  /** The default sort of all individuals, always in the non-sorted case */  
  static const unsigned DEFAULT_SORT_CON=0;
  /** Boolean sort */
  static const unsigned BOOL_SRT_CON=1;
  /** sort of integers */
  static const unsigned INTEGER_SRT_CON=2;
  /** sort of rationals */
  static const unsigned RATIONAL_SRT_CON=3;
  /** sort of reals */  
  static const unsigned REAL_SRT_CON=4;
  /** this is not a sort, it is just used to denote the first index of a user-define sort */
  static const unsigned FIRST_USER_CON=5;
  
  class Symbol {
  
  protected:
    /** print name */
    std::string _name;

    // both _arity and _typeArgsArity could be recovered from _type. Storing directly here as well for convenience

    /** arity */
    unsigned _arity;
    /** arity of type arguments */
    unsigned _typeArgsArity;

    /** Either a FunctionType of a PredicateType object */
    mutable OperatorType* _type;
    /** List of distinct groups the constant is a member of, all members of a distinct group should be distinct from each other */
    List<unsigned>* _distinctGroups;
    /** number of times it is used in the problem */
    unsigned _usageCount;
    /** number of units it is used in in the problem */
    unsigned _unitUsageCount;

    /** the object is of type InterpretedSymbol */
    unsigned _interpreted : 1;
    unsigned _linMul : 1;
    /** symbol that doesn't come from input problem, but was introduced by Vampire */
    unsigned _introduced : 1;
    /** protected symbols aren't subject to any kind of preprocessing elimination */
    unsigned _protected : 1;
    /** clauses with only skipped symbols will not be output as symbol eliminating */
    unsigned _skip : 1;
    /** marks propositional predicate symbols that are labels to 
        be used as names during consequence finding or function relationship finding */
    unsigned _label : 1;
    /** marks predicates that are equality proxy */
    unsigned _equalityProxy : 1;
    /** was flipped **/ 
    unsigned _wasFlipped : 1;
    /** used in coloured proofs and interpolation */
    unsigned _color : 2;
    /** predicate introduced for query answering */
    unsigned _answerPredicate : 1;
    /** marks term algebra constructors */
    unsigned _termAlgebraCons : 1;
    /** marks term algebra destructors */
    unsigned _termAlgebraDest : 1;
    /** marks term algebra discriminators */
    unsigned _termAlgebraDiscriminator : 1;
    /** if used in the goal **/
    unsigned _inGoal : 1;
    /** if used in a unit **/
    unsigned _inUnit : 1;
    /** if induction skolem **/
    unsigned _inductionSkolem : 1;
    /** if skolem function in general **/
    unsigned _skolem : 1;
    /** if does not need congruence axioms with equality proxy */
    unsigned _skipCongruence : 1;
    /** if tuple sort */
    unsigned _tuple : 1;
    /** proxy type */
    Proxy _prox;
    int _deBruijnIndex;

  public:
    /** standard constructor */
    Symbol(const std::string& name, unsigned arity, bool interpreted, bool preventQuoting, bool super);
    void destroyFnSymbol();
    void destroyPredSymbol();
    void destroyTypeConSymbol();

    void addColor(Color color);
    /** mark symbol that doesn't come from input problem, but was introduced by Vampire */
    void markIntroduced() { _introduced=1; }
    /** remove the marking that the symbol was introduced, it has now been found in the input
        we should be careful that the previously introduced symbols are renamed elsewhere */
    void unmarkIntroduced(){ _introduced=0; }
    /** mark the symbol as protected so it is not being eliminated by preprocessing */
    void markProtected() { _protected=1; }
    /** mark the symbol as skip for the purpose of symbol elimination */
    void markSkip() { _skip=1; }
    /** mark the symbol as name for consequence finding */
    void markLabel() { ASS_EQ(arity(), 0); _label=1; markProtected(); }
    /** mark symbol to be an answer predicate */
    void markAnswerPredicate() { _answerPredicate=1; markProtected(); }
    /** mark predicate to be an equality proxy */
    void markEqualityProxy() { _equalityProxy=1; }
    /** mark predicate as (polarity) flipped */
    void markFlipped() { _wasFlipped=1; }
    void markLinMul() { _linMul=1; }
    /** mark symbol as a term algebra constructor */
    void markTermAlgebraCons() { _termAlgebraCons=1; }
    /** mark symbol as a term algebra destructor */
    void markTermAlgebraDest() { _termAlgebraDest=1; }
    /** mark symbol as a term algebra discriminator */
    void markTermAlgebraDiscriminator() { _termAlgebraDiscriminator=1; }

    /** return true iff symbol is marked as skip for the purpose of symbol elimination */
    bool skip() const { return _skip; }
    /** return true iff the symbol is marked as name predicate
        for consequence finding */
    bool label() const { return _label; }
    /** return the colour of the symbol */
    Color color() const { return static_cast<Color>(_color); }
    /** Return the arity of the symbol
     * this includes the term as well as the type arguments of the symbol
     */
    inline unsigned arity() const { return _arity; }
    /* the number of term arguments for this symbol */
    inline unsigned numTermArguments() const { return arity() - numTypeArguments(); }
    /** Return the type argument arity of the symbol. Only accurate once type has been set. */
    inline unsigned numTypeArguments() const 
    { 
      if(name() == "="){ 
        //for some reason, equality is never assigned a type (probably because it is poly)
        return 0; 
      }
      ASS_REP(_type, name()); 
      return _typeArgsArity; 
    }
    /** Return the name of the symbol */
    inline const std::string& name() const { return _name; }
    /** Return true iff the object is of type InterpretedSymbol */
    inline bool interpreted() const { return _interpreted; }
    /** Return true iff the symbol doesn't come from input problem but was introduced by Vampire */
    inline bool introduced() const { return _introduced; }
    /** Return true iff the symbol is must not be eliminated by proprocessing */
    inline bool protectedSymbol() const { return _protected; }
    /** Return true iff symbol is an answer predicate */
    inline bool answerPredicate() const { return _answerPredicate; }
    /** Return true iff symbol is an equality proxy */
    inline bool equalityProxy() const { return _equalityProxy; }
    /** Return true iff symbol was polarity flipped */
    inline bool wasFlipped() const { return _wasFlipped; }
    /** Return true iff symbol is a term algebra constructor */
    inline bool termAlgebraCons() const { return _termAlgebraCons; }
    /** Return true iff symbol is a term algebra destructor */
    inline bool termAlgebraDest() const { return _termAlgebraDest; }
    /** Return true iff symbol is a term algebra destructor */
    inline bool termAlgebraDiscriminator() const { return _termAlgebraDiscriminator; }

    /** Increase the usage count of this symbol **/
    inline void incUsageCnt(){ _usageCount++; }
    /** Return the usage count of this symbol **/
    inline unsigned usageCnt() const { return _usageCount; }
    /** Reset usage count to zero, to start again! **/
    inline void resetUsageCnt(){ _usageCount=0; }

    inline void incUnitUsageCnt(){ _unitUsageCount++;}
    inline unsigned unitUsageCnt() const { return _unitUsageCount; }
    inline void resetUnitUsageCnt(){ _unitUsageCount=0;}

    inline void markInGoal(){ _inGoal=1; }
    inline bool inGoal(){ return _inGoal; }
    inline void markInUnit(){ _inUnit=1; }
    inline bool inUnit(){ return _inUnit; }

    inline void markSkolem(){ _skolem = 1;}
    inline bool skolem(){ return _skolem; }

    inline void markSkipCongruence() { _skipCongruence = 1; }
    inline bool skipCongruence() { return _skipCongruence; }

    inline void markTuple(){ _tuple = 1; }
    inline bool tupleSort(){ return _tuple; }

    inline void setProxy(Proxy prox){ _prox = prox; }
    inline Proxy proxy(){ return _prox; }

    void setDeBruijnIndex(int index) {
      _deBruijnIndex = index;
    }

    Option<unsigned> deBruijnIndex() const {
      if (_deBruijnIndex > -1)
        return Option<unsigned>(static_cast<unsigned>(_deBruijnIndex));

      return {};
    }

    inline void markInductionSkolem(){ _inductionSkolem=1; _skolem=1;}
    inline bool inductionSkolem(){ return _inductionSkolem;}
      
    /** Return true if symbol is an integer constant */
    inline bool integerConstant() const
    { return interpreted() && arity()==0 && fnType()->result()==AtomicSort::intSort(); }
    /** Return true if symbol is a rational constant */
    inline bool rationalConstant() const
    { return interpreted() && arity()==0 && fnType()->result()==AtomicSort::rationalSort(); }
    /** Return true if symbol is a real constant */
    inline bool realConstant() const
    { return interpreted() && arity()==0 && fnType()->result()==AtomicSort::realSort(); }

  private:
    bool numeralConstant(RealConstantType*) const { return realConstant(); }
    bool numeralConstant(RationalConstantType*) const { return rationalConstant(); }
    bool numeralConstant(IntegerConstantType*) const { return integerConstant(); }
  public:

    /** template version of {integer,rational,real}Constant */
    template<class Number> bool numeralConstant() const
    { return numeralConstant((Number*)nullptr); }

    /** return true if an interpreted number */
    inline bool interpretedNumber() const
    { return integerConstant() || rationalConstant() || realConstant(); }

    inline bool linMul() const
    { return _linMul; }

    /** Return value of an integer constant */
    inline IntegerConstantType const& integerValue() const
    { ASS(integerConstant()); return static_cast<const IntegerSymbol*>(this)->_intValue; }
    /** Return value of a rational constant */
    inline RationalConstantType const& rationalValue() const
    { ASS(rationalConstant()); return static_cast<const RationalSymbol*>(this)->_ratValue; }
    /** Return value of a real constant */
    inline RealConstantType const& realValue() const
    { ASS(realConstant()); return static_cast<const RealSymbol*>(this)->_realValue; }

  private:
    RealConstantType const& numeralValue(RealConstantType*) const { return realValue(); }
    RationalConstantType const& numeralValue(RationalConstantType*) const { return rationalValue(); }
    IntegerConstantType const& numeralValue(IntegerConstantType*) const { return integerValue(); }
  public:

    /** template version of {integer,rational,real}Value */
    template<class Number> auto const& numeralValue() const
    { return numeralValue((Number*)nullptr); }

    const List<unsigned>* distinctGroups() const { return _distinctGroups; }
    /** This takes the symbol number of this symbol as the symbol doesn't know it
        Note that this should only be called on a constant **/
    void addToDistinctGroup(unsigned group,unsigned this_number);
    friend std::ostream& operator<<(std::ostream& out, const Signature::Symbol& self)
    { 
      out << self.name() << ": "; 
      if (self._type) {
        out << *self._type;
      } else {
        out << "<type not (yet) set>";
      }
      return out;
    }

    void setType(OperatorType* type);
    void forceType(OperatorType* type);
    OperatorType* fnType() const;
    OperatorType* predType() const;
    OperatorType* typeConType() const;
  }; // class Symbol

  class InterpretedSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    Interpretation _interp;

  public:

    InterpretedSymbol(const std::string& name, Interpretation interp)
    : Symbol(name, 
        /* arity */ Theory::getArity(interp), 
        /*       interpreted */ true, 
        /*    preventQuoting */ false, 
        /*             super */ false),
      _interp(interp)
    {
    }

    /** Return the interpreted function that corresponds to this symbol */
    inline Interpretation getInterpretation() const { ASS_REP(interpreted(), _name); return _interp; }
  };

  class AnyLinMulSym 
    : public Symbol {
  public:
    enum Type { Int, Rat, Real, } type;
  private:
    static Type typeOf(IntegerConstantType*) { return Int; }
    static Type typeOf(RationalConstantType*) { return Rat; }
    static Type typeOf(RealConstantType*) { return Real; }

    static auto sortOf(IntegerConstantType *) { return AtomicSort::intSort(); }
    static auto sortOf(RationalConstantType *) { return AtomicSort::rationalSort(); }
    static auto sortOf(RealConstantType *) { return AtomicSort::realSort(); }

  public:

    template<class Numeral>
    auto isType() const { return typeOf<Numeral>() == type; }
    template<class Numeral>
    static auto typeOf() { return typeOf((Numeral*)0); }
    template<class Numeral>
    static auto sortOf() { return sortOf((Numeral*)0); }

    template<class... Args>
    AnyLinMulSym(Type type, Args... args) : Symbol(std::move(args)...), type(type) 
    { markLinMul(); }
  };

  template<class Numeral>
  class LinMulSym
  : public AnyLinMulSym
  {
    friend class Signature;
    friend class Symbol;
    Numeral _value;

  public:
    static std::string name(Numeral n) { return Output::toString(n); }
    LinMulSym(Numeral val)
    : AnyLinMulSym(
        AnyLinMulSym::typeOf<Numeral>(),
        name(val),
        /*             arity */ 1, 
        /*       interpreted */ false, 
        /*    preventQuoting */ true, 
        /*             super */ false),
      _value(std::move(val))
    {
      setType(OperatorType::getFunctionType({ AnyLinMulSym::sortOf<Numeral>() } , AnyLinMulSym::sortOf<Numeral>()));
    }
  };


  class IntegerSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    IntegerConstantType _intValue;

  public:
    IntegerSymbol(IntegerConstantType val)
    : Symbol(Output::toString(val),
        /*             arity */ 0, 
        /*       interpreted */ true, 
        /*    preventQuoting */ false, 
        /*             super */ false),
      _intValue(std::move(val))
    {
      setType(OperatorType::getConstantsType(AtomicSort::intSort()));
    }
  };

  class RationalSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    RationalConstantType _ratValue;

  public:
    RationalSymbol(RationalConstantType val)
    : Symbol(Output::toString(val),
        /*             arity */ 0, 
        /*       interpreted */ true, 
        /*    preventQuoting */ false, 
        /*             super */ false),
       _ratValue(std::move(val))
    {
      setType(OperatorType::getConstantsType(AtomicSort::rationalSort()));
    }
  };

  class RealSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    RealConstantType _realValue;

  public:
    RealSymbol(const RealConstantType& val);
  };

  //////////////////////////////////////
  // Uninterpreted symbol declarations
  //

  unsigned addPredicate(const std::string& name,unsigned arity,bool& added);
  unsigned addTypeCon(const std::string& name,unsigned arity,bool& added);
  unsigned addFunction(const std::string& name,unsigned arity,bool& added);

  /**
   * If a predicate with this name and arity exists, return its number.
   * Otherwise, add a new one and return its number.
   *
   * @param name name of the symbol
   * @param arity arity of the symbol
   * @since 07/05/2007 Manchester
   */
  unsigned addPredicate(const std::string& name,unsigned arity)
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
  unsigned addFunction(const std::string& name,unsigned arity)
  {
    bool added;
    return addFunction(name,arity,added);
  }
  /**
   * If a unique string constant with this name and arity exists, return its number.
   * Otherwise, add a new one and return its number.
   *
   * The added constant is of default ($i) sort.
   */
  unsigned addStringConstant(const std::string& name);
  unsigned addFreshFunction(unsigned arity, const char* prefix, const char* suffix = 0);
  unsigned addSkolemFunction(unsigned arity,const char* suffix = 0);
  unsigned addFreshTypeCon(unsigned arity, const char* prefix, const char* suffix = 0);
  unsigned addSkolemTypeCon(unsigned arity,const char* suffix = 0);
  unsigned addFreshPredicate(unsigned arity, const char* prefix, const char* suffix = 0);
  unsigned addSkolemPredicate(unsigned arity,const char* suffix = 0);
  unsigned addNamePredicate(unsigned arity);
  unsigned addNameFunction(unsigned arity);
  void addEquality();
  unsigned getApp();
  unsigned getLam();
  unsigned getDiff();
  unsigned getChoice();
  unsigned getDeBruijnIndex(int index);
  unsigned getPlaceholder();
  unsigned getDefPred();
  /**
   * For a function f with result type t, this introduces a predicate
   * $def_f with the type t x t. This is used to track expressions of
   * the form f(s) = s' as $def_f(f(s),s') through preprocessing.
   */
  unsigned getFnDef(unsigned fn);
  /**
   * For a predicate p, this introduces a predicate $def_p with the same signature,
   * which is used to track a predicate definition "headers" through preprocessing.
   */
  unsigned getBoolDef(unsigned fn);

 private:
  Symbol* newNumeralConstantSymbol(IntegerConstantType n) 
  { return new IntegerSymbol(std::move(n)); }

  Symbol* newNumeralConstantSymbol(RationalConstantType n) 
  { return new RationalSymbol(std::move(n)); }

  Symbol* newNumeralConstantSymbol(RealConstantType n) 
  { return new RealSymbol(std::move(n)); }
 public:

  // Interpreted symbol declarations

  template<class Numeral>
  unsigned addNumeralConstant(Numeral number_) {
    auto key = SymbolKey(std::make_pair(std::move(number_), unsigned(0)));
    unsigned result;
    if (_funNames.find(key,result)) {
      return result;
    }
    result = _funs.length();
    // copy number out of key again
    auto number = key.as<std::pair<Numeral, unsigned>>()->first;
    noteOccurrence(number);
    Symbol* sym = newNumeralConstantSymbol(std::move(number));
    _funs.push(sym);
    _funNames.insert(key,result);
    return result;
  }

 private:
  void noteOccurrence(IntegerConstantType const&)  { _integers++; }
  void noteOccurrence(RationalConstantType const&)  { _rationals++; }
  void noteOccurrence(RealConstantType const&)  { _reals++; }
 public:

  template<class Numeral>
  unsigned addLinMul(Numeral const& number) {
    auto key = SymbolKey(std::make_pair(number, unsigned(1)));
    unsigned result;
    if (_funNames.find(key, result)) {
      return result;
    }
    noteOccurrence(number);
    result = _funs.length();
    Symbol* sym = new LinMulSym<Numeral>(number);
    auto s = AnyLinMulSym::sortOf<Numeral>();
    sym->setType(OperatorType::getFunctionType({s}, s));
    _funs.push(sym);
    _funNames.insert(key,result);
    return result;
  }

  template<class Numeral>
  static Lib::Option<LinMulSym<Numeral>&> tryLinMulSym(Symbol* sym) {
    return someIf(sym->linMul() && static_cast<LinMulSym<Numeral>*>(sym)->template isType<Numeral>(),
        [&]() -> LinMulSym<Numeral>& { return *static_cast<LinMulSym<Numeral>*>(sym); });
  }

  template<class Numeral>
  Lib::Option<Numeral const&> tryLinMul(unsigned f) {
    if (f >= Term::SPECIAL_FUNCTOR_LOWER_BOUND) return {};
    if (auto sym = tryLinMulSym<Numeral>(getFunction(f))) {
      return Option<Numeral const&>(sym->_value);
    } else {
      return {};
    }
  }


  unsigned addInterpretedFunction(Interpretation itp, OperatorType* type, const std::string& name);
  unsigned addInterpretedFunction(Interpretation itp, const std::string& name)
  {
    ASS(!Theory::isPolymorphic(itp));
    return addInterpretedFunction(itp,Theory::getNonpolymorphicOperatorType(itp),name);
  }

  unsigned addInterpretedPredicate(Interpretation itp, OperatorType* type, const std::string& name);
  unsigned addInterpretedPredicate(Interpretation itp, const std::string& name)
  {
    ASS(!Theory::isPolymorphic(itp));
    return addInterpretedPredicate(itp,Theory::getNonpolymorphicOperatorType(itp),name);
  }

  unsigned getInterpretingSymbol(Interpretation interp, OperatorType* type);
  unsigned getInterpretingSymbol(Interpretation interp)
  {
    ASS(!Theory::isPolymorphic(interp));
    return getInterpretingSymbol(interp,Theory::getNonpolymorphicOperatorType(interp));
  }

  /** Return true iff there is a symbol interpreted by Interpretation @b interp */
  bool haveInterpretingSymbol(Interpretation interp, OperatorType* type) const {
    return _iSymbols.find(std::make_pair(interp,type));
  }
  bool haveInterpretingSymbol(Interpretation interp)
  {
    ASS(!Theory::isPolymorphic(interp));
    return haveInterpretingSymbol(interp,Theory::getNonpolymorphicOperatorType(interp));
  }

  /** return the name of a function with a given number */
  const std::string& functionName(int number);
  /** return the name of a predicate with a given number */
  const std::string& predicateName(int number)
  {
    return _preds[number]->name();
  }
  /** return the name of a type constructor with a given number */
  const std::string& typeConName(int number)
  {
    return _typeCons[number]->name();
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

  const unsigned typeConArity(int number)
  {
    return _typeCons[number]->arity();
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
  bool isPredicateName(std::string name, unsigned arity)
  {
    auto symbolKey = key(name,arity);
    unsigned tmp;
    return _predNames.find(symbolKey,tmp);
  }

  void addChoiceOperator(unsigned fun){
    _choiceSymbols.insert(fun);
  }

  bool isChoiceOperator(unsigned fun){
    return _choiceSymbols.contains(fun);
  }

  DHSet<unsigned>* getChoiceOperators(){
    return &_choiceSymbols;
  }

  /** return the number of functions */
  unsigned functions() const { return _funs.length(); }
  /** return the number of predicates */
  unsigned predicates() const { return _preds.length(); }
  /** return the number of typecons */
  unsigned typeCons() const { return _typeCons.length(); }

  /** Return the function symbol by its number */
  inline Symbol* getFunction(unsigned n)
  {
    ASS_REP(n < _funs.length(),n);
    return _funs[n];
  } // getFunction
  /** Return the predicate symbol by its number */
  inline Symbol* getPredicate(unsigned n)
  {
    ASS(n < _preds.length());
    return _preds[n];
  } // getPredicate
  inline Symbol* getTypeCon(unsigned n)
  {
    ASS(n < _typeCons.length());
    return _typeCons[n];
  }

  static inline bool isEqualityPredicate(unsigned p)
  {
    // we make sure equality is always 0
    return (p == 0); // see the ASSERT in Signature::Signature
  }

  Signature();
  ~Signature();

  bool functionExists(const std::string& name,unsigned arity) const;
  bool predicateExists(const std::string& name,unsigned arity) const;
  bool typeConExists(const std::string& name,unsigned arity) const;

  /** true if there are user defined sorts */
  bool hasSorts() const{
    return typeCons() > FIRST_USER_CON;
  }

  bool isDefaultSortCon(unsigned con) const{
    return con < FIRST_USER_CON;
  }

  bool isInterpretedNonDefault(unsigned con) const{
    return con < FIRST_USER_CON && con != DEFAULT_SORT_CON;    
  }

  bool isNonDefaultCon(unsigned con) const{
    return con >= FIRST_USER_CON;    
  }

  bool isBoolCon(unsigned con) const{
    return con == BOOL_SRT_CON;    
  }

  bool isTupleCon(unsigned con) {
    return getTypeCon(con)->tupleSort();
  }

  bool isArrayCon(unsigned con) const{
    //second part of conditions ensures that _arrayCon
    //has been initialised.
    return con == _arrayCon && _arrayCon != UINT_MAX;
  }

  bool isArrowCon(unsigned con) const{
    return con == _arrowCon && _arrowCon != UINT_MAX;
  }
  
  bool isAppFun(unsigned fun) const{
    return fun == _appFun && _appFun != UINT_MAX;
  }

  bool isLamFun(unsigned fun) const {
    return fun == _lamFun && _lamFun != UINT_MAX;
  }

  bool isChoiceFun(unsigned fun) const{
    return fun == _choiceFun && _choiceFun != UINT_MAX;
  }

  bool isPlaceholder(unsigned fun) const{
    return fun == _placeholderFun && _placeholderFun != UINT_MAX;
  }

  bool isDefPred(unsigned p) const {
    return p == _defPred && _defPred != UINT_MAX;
  }

  bool isFnDefPred(unsigned p) const{
    return _fnDefPreds.contains(p);
  }

  bool isBoolDefPred(unsigned p, unsigned& orig) const {
    return _boolDefPreds.find(p, orig);
  }

  bool tryGetFunctionNumber(const std::string& name, unsigned arity, unsigned& out) const;
  bool tryGetPredicateNumber(const std::string& name, unsigned arity, unsigned& out) const;
  unsigned getFunctionNumber(const std::string& name, unsigned arity) const;
  unsigned getPredicateNumber(const std::string& name, unsigned arity) const;

  typedef SmartPtr<Stack<unsigned>> DistinctGroupMembers;
  
  Unit* getDistinctGroupPremise(unsigned group);
  unsigned createDistinctGroup(Unit* premise = 0);
  void addToDistinctGroup(unsigned constantSymbol, unsigned groupId);
  bool hasDistinctGroups(){ return _distinctGroupsAddedTo; }
  void noDistinctGroupsLeft(){ _distinctGroupsAddedTo=false; }
  Stack<DistinctGroupMembers> &distinctGroupMembers(){ return _distinctGroupMembers; }

  bool hasTermAlgebras() { return !_termAlgebras.isEmpty(); }
  bool hasDefPreds() const { return !_fnDefPreds.isEmpty() || !_boolDefPreds.isEmpty(); }
      
  static SymbolKey key(const std::string& name,int arity);

  /** the number of string constants */
  unsigned strings() const {return _strings;}
  /** the number of integer constants */
  unsigned integers() const {return _integers;}
  /** the number of rational constants */
  unsigned rationals() const {return _rationals;}
  /** the number of real constants */
  unsigned reals() const {return _reals;}

  static const unsigned STRING_DISTINCT_GROUP;

  unsigned getFoolConstantSymbol(bool isTrue){ 
    if(!_foolConstantsDefined){
      _foolFalse = addFunction("$$false",0); 
      getFunction(_foolFalse)->setType(OperatorType::getConstantsType(AtomicSort::boolSort()));
      _foolTrue = addFunction("$$true",0);
      getFunction(_foolTrue)->setType(OperatorType::getConstantsType(AtomicSort::boolSort()));
      _foolConstantsDefined=true;
    }
    return isTrue ? _foolTrue : _foolFalse;
  }
  bool isFoolConstantSymbol(bool isTrue, unsigned number){
    if(!_foolConstantsDefined) return false;
    return isTrue ? number==_foolTrue : number==_foolFalse;
  }

  unsigned getDefaultSort(){
    bool added = false;
    unsigned individualSort = addTypeCon("$i",0, added);
    if(added){
      getTypeCon(individualSort)->setType(OperatorType::getConstantsType(AtomicSort::superSort()));
    }
    return individualSort;
  }

  unsigned getBoolSort(){
    bool added = false;
    unsigned boolSort = addTypeCon("$o",0, added);
    if(added){
      getTypeCon(boolSort)->setType(OperatorType::getConstantsType(AtomicSort::superSort()));
    }
    return boolSort;
  }

  unsigned getRealSort(){
    bool added = false;
    unsigned realSort = addTypeCon("$real",0, added);
    if(added){
      getTypeCon(realSort)->setType(OperatorType::getConstantsType(AtomicSort::superSort()));
    }
    return realSort;
  }

  unsigned getIntSort(){
    bool added = false;
    unsigned intSort = addTypeCon("$int",0, added);
    if(added){
      getTypeCon(intSort)->setType(OperatorType::getConstantsType(AtomicSort::superSort()));
    }
    return intSort;
  }  

  unsigned getRatSort(){
    bool added = false;
    unsigned ratSort = addTypeCon("$rat",0, added);
    if(added){
      getTypeCon(ratSort)->setType(OperatorType::getConstantsType(AtomicSort::superSort()));
    }
    return ratSort;    
  }

  unsigned getArrowConstructor(){
    bool added = false;
    unsigned arrow = addTypeCon("sTfun",2, added);
    if(added){
      _arrowCon = arrow;
      TermList ss = AtomicSort::superSort();
      Symbol* arr = getTypeCon(arrow);
      arr->setType(OperatorType::getFunctionType({ss, ss}, ss));
    }
    return arrow;    
  }

  unsigned getArrayConstructor(){
    bool added = false;
    unsigned array = addTypeCon("Array",2, added);
    if(added){
      _arrayCon = array;
      TermList ss = AtomicSort::superSort();
      Symbol* arr = getTypeCon(array);
      arr->setType(OperatorType::getFunctionType({ss, ss}, ss));
    }
    return array;    
  }

  unsigned getTupleConstructor(unsigned arity){
    bool added = false;
    //TODO make the name unique
    unsigned tuple = addTypeCon("Tuple", arity, added);
    if(added){
      Symbol* tup = getTypeCon(tuple);
      tup->setType(OperatorType::getTypeConType(arity));
      tup->markTuple();
    }
    return tuple;    
  }  

  unsigned getEqualityProxy(){
    bool added = false;
    unsigned eqProxy = addFunction("vEQ",1, added);
    if(added){
      TermList tv = TermList(0, false);
      TermList result = AtomicSort::arrowSort(tv, tv, AtomicSort::boolSort());
      Symbol * sym = getFunction(eqProxy);
      sym->setType(OperatorType::getConstantsType(result, 1));
      sym->setProxy(Proxy::EQUALS);
    }
    return eqProxy;  
  }

  unsigned getBinaryProxy(const std::string& name) {
    ASS(name == "vIMP" || name == "vAND" || name == "vOR" || name == "vIFF" || name == "vXOR");
    bool added = false;
    
    static constexpr auto convert = [](const std::string& name) {
      if (name == "vIMP") return Proxy::IMP;
      if (name == "vAND") return Proxy::AND;
      if (name == "vOR") return Proxy::OR;
      if (name == "vIFF") return Proxy::IFF;
      return Proxy::XOR;
    };

    unsigned proxy = addFunction(name, 0, added);
    if (added) {
      auto bs = AtomicSort::boolSort();
      auto result = AtomicSort::arrowSort(bs, bs, bs);
      auto sym = getFunction(proxy);
      sym->setType(OperatorType::getConstantsType(result));
      sym->setProxy(convert(name));
    }
    return proxy;  
  }

  unsigned getNotProxy(){
    bool added = false;
    unsigned notProxy = addFunction("vNOT",0, added);
    if(added){
      TermList bs = AtomicSort::boolSort();
      TermList result = AtomicSort::arrowSort(bs, bs);
      Symbol * sym = getFunction(notProxy);
      sym->setType(OperatorType::getConstantsType(result));
      sym->setProxy(Proxy::NOT);
    }
    return notProxy;  
  } //TODO merge with above?


  unsigned getPiSigmaProxy(std::string name){
    bool added = false;
    unsigned proxy = addFunction(name,1, added);
    if (added) {
      auto tv = TermList(0, false);
      auto result = AtomicSort::arrowSort(tv, AtomicSort::boolSort());
      result = AtomicSort::arrowSort(result, AtomicSort::boolSort());
      auto sym = getFunction(proxy);
      sym->setType(OperatorType::getConstantsType(result, 1));
      sym->setProxy(name == "vPI" ? Proxy::PI : Proxy::SIGMA);
    }
    return proxy;  
  } //TODO merge with above?  

  //TODO make all these names protected

  void incrementFormulaCount(Term* t);
  void decrementFormulaCount(Term* t);
  void formulaNamed(Term* t);
  unsigned formulaCount(Term* t);


  bool isTermAlgebraSort(TermList sort) { return sort.isTerm() && _termAlgebras.find(sort.term()->functor()); }
  Shell::TermAlgebra *getTermAlgebraOfSort(TermList sort) {
    ASS(sort.isTerm() && sort.term()->isSort());
    return _termAlgebras.get(sort.term()->functor());
  }
  void addTermAlgebra(Shell::TermAlgebra *ta) { _termAlgebras.insert(ta->sort().term()->functor(), ta); }
  VirtualIterator<Shell::TermAlgebra*> termAlgebrasIterator() const { return _termAlgebras.range(); }
  Shell::TermAlgebraConstructor* getTermAlgebraConstructor(unsigned functor);

  void recordDividesNvalue(TermList n){
    _dividesNvalues.push(n);
  }
  Stack<TermList>& getDividesNvalues(){ return _dividesNvalues; }

  static bool symbolNeedsQuoting(std::string name, bool interpreted, unsigned arity);

private:
  Stack<TermList> _dividesNvalues;
  DHMap<Term*, int> _formulaCounts;

  bool _foolConstantsDefined;
  unsigned _foolTrue;
  unsigned _foolFalse;

  static bool isProtectedName(std::string name);
  static bool charNeedsQuoting(char c, bool first);
  /** Stack of function symbols */
  Stack<Symbol*> _funs;
  /** Stack of predicate symbols */
  Stack<Symbol*> _preds;
  /** Stack of type constructor symbols */  
  Stack<Symbol*> _typeCons;

  DHSet<unsigned> _choiceSymbols;

  SymbolMap _funNames;
  SymbolMap _predNames;
  SymbolMap _typeConNames;
  /** Map for the arity_check options: maps symbols to their arities */
  Map<std::string, unsigned> _arityCheck;
  /** Last number used for fresh functions and predicates */
  int _nextFreshSymbolNumber;

  /** Map from symbol names to variable numbers*/
  SymbolMap _varNames;

  // Store the premise of a distinct group for proof printing, if 0 then group is input
  Stack<Unit*> _distinctGroupPremises;

  // We only store members up until a hard-coded limit i.e. the limit at which we will expand the group
  Stack<DistinctGroupMembers> _distinctGroupMembers;
  // Flag to indicate if any distinct groups have members
  bool _distinctGroupsAddedTo;

  /**
   * Map from MonomorphisedInterpretation values to function and predicate symbols representing them
   *
   * We mix here function and predicate symbols, but it is not a problem, as
   * the MonomorphisedInterpretation value already determines whether we deal with a function
   * or a predicate.
   */
  DHMap<Theory::MonomorphisedInterpretation, unsigned> _iSymbols;

  /** the number of string constants */
  unsigned _strings;
  /** the number of integer constants */
  unsigned _integers;
  /** the number of rational constants */
  unsigned _rationals;
  /** the number of real constants */
  unsigned _reals;

  unsigned _arrayCon;
  unsigned _arrowCon;
  unsigned _appFun;
  unsigned _lamFun;
  unsigned _choiceFun;
  unsigned _placeholderFun;
  unsigned _defPred;
  DHSet<unsigned> _fnDefPreds;
  DHMap<unsigned,unsigned> _boolDefPreds;

  /**
   * Map from type constructor functor to the associated term algebra, if applicable for the sort.
   * If the term algebra is polymorphic, it contains the general type, ctors, dtors, etc.
   * For a term algebra instance, this map gives the general term algebra based on the top-level
   * functor of its sort, the ctors and dtors still have to be instantiated to the right instances.
   */
  DHMap<unsigned, Shell::TermAlgebra*> _termAlgebras;

  //TODO Why are these here? They are not used anywhere. AYB
  //void defineOptionTermAlgebra(unsigned optionSort);
  //void defineEitherTermAlgebra(unsigned eitherSort);
}; // class Signature

}

#endif // __Signature__
