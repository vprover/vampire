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
 * @file Term.hpp
 * Defines class Term (also serving as term arguments)
 *
 * @since 18/04/2006 Bellevue
 * @since 06/05/2007 Manchester, changed into a single class instead of three
 */

#ifndef __Term__
#define __Term__

#include <cstdlib>
#include <iosfwd>
#include <utility>

#include "Forwards.hpp"
#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VString.hpp"

#define TERM_DIST_VAR_UNKNOWN 0x3FFFFF

namespace Kernel {

using namespace std;
using namespace Lib;

/** Tag denoting the kind of this term
 * @since 19/02/2008 Manchester, moved outside of the Term class
 */
enum TermTag {
  /** reference to another term */
  REF = 0u,
  /** ordinary variable */
  ORD_VAR = 1u,
  /** (function) symbol */
  FUN = 2u,
  /** special variable */
  SPEC_VAR = 3u,
};

bool operator<(const TermList& lhs, const TermList& rhs);

/**
 * Class containing either a pointer to a compound term or
 * a variable number or a functor.
 */
class TermList {
public:
  CLASS_NAME(TermList)
  static const unsigned SPEC_UPPER_BOUND = 10000000;
  /** dummy constructor, does nothing */
  TermList() {}
  /** creates a term list and initialises its content with data */
  explicit TermList(size_t data) : _content(data) {}
  /** creates a term list containing a pointer to a term */
  explicit TermList(Term* t) : _term(t) {}
  /** creates a term list containing a variable. If @b special is true, then the variable
   * will be "special". Special variables are also variables, with a difference that a
   * special variables and ordinary variables have an empty intersection */
  TermList(unsigned var, bool special)
  {
    if (special) {
      makeSpecialVar(var);
    }
    else {
      makeVar(var);
    }
  }

  /** the tag */
  inline TermTag tag() const { return (TermTag)(_content & 0x0003); }
  /** the term list is empty */
  inline bool isEmpty() const
  { return tag() == FUN; }
  /** the term list is non-empty */
  inline bool isNonEmpty() const
  { return tag() != FUN; }
  /** next term in this list */
  inline TermList* next()
  { return this-1; }
  /** next term in this list */
  inline const TermList* next() const
  { return this-1; }
  /** the term contains a variable as its head */
  inline bool isVar() const { return (_content & 0x0001) == 1; }
  /** the term contains an ordinary variable as its head */
  inline bool isOrdinaryVar() const { return tag() == ORD_VAR; }
  /** the term contains a special variable as its head */
  inline bool isSpecialVar() const { return tag() == SPEC_VAR && var() < SPEC_UPPER_BOUND; }

  inline bool isVSpecialVar() const { return tag() == SPEC_VAR && var() > SPEC_UPPER_BOUND; }
  /** return the variable number */
  inline unsigned var() const
  { ASS(isVar()); return _content / 4; }
  /** the term contains reference to Term class */
  inline bool isTerm() const
  { return tag() == REF; }
  inline const Term* term() const
  { ASS(isTerm()); return _term; }
  inline Term* term()
  { ASS(isTerm()); return _term; }
  /** True of the terms have the same content. Useful for comparing
   * arguments of shared terms. */
  inline bool sameContent(const TermList* t) const
  { return _content == t->_content ; }
  /** return the content, useful for e.g., term argument comparison */
  inline size_t content() const { return _content; }
  vstring toString(bool topLevel = true) const;
  /** make the term into an ordinary variable with a given number */
  inline void makeVar(unsigned vnumber)
  { _content = vnumber * 4 + ORD_VAR; }
  /** make the term into a special variable with a given number */
  inline void makeSpecialVar(unsigned vnumber)
  { _content = vnumber * 4 + SPEC_VAR; }
  /** make the term empty (so that isEmpty() returns true) */
  inline void makeEmpty()
  { _content = FUN; }
  /** make the term into a reference */
  inline void setTerm(Term* t)
  { _term = t; }
  static bool sameTop(TermList ss, TermList tt);
  static bool sameTopFunctor(TermList ss, TermList tt);
  static bool equals(TermList t1, TermList t2);
  static bool allShared(TermList* args);
  static TermList var(unsigned var, bool special = false) { return TermList(var, special); }
  /** if not var, the inner term must be shared */
  unsigned weight() const;
  /** returns true if this termList is wrapping a higher-order "arrow" sort */
  bool isArrowSort();
  bool isBoolSort();
  bool isArraySort();
  bool isTupleSort();
  bool isApplication() const;
  bool containsSubterm(TermList v);
  bool containsAllVariablesOf(TermList t);
  bool containsAllVariableOccurrencesOf(TermList t);

  bool isSafe() const;

  VList* freeVariables() const;
  bool isFreeVariable(unsigned var) const;

#if VDEBUG
  void assertValid() const;
#endif

  inline bool operator==(const TermList& t) const
  { return _content==t._content; }
  inline bool operator!=(const TermList& t) const
  { return _content!=t._content; }

  friend bool operator<(const TermList& lhs, const TermList& rhs);

private:
  vstring asArgsToString() const;

  union {
    /** reference to another term */
    Term* _term;
    /** raw content, can be anything */
    size_t _content;
    /** Used by Term, storing some information about the term using bits */
    struct {
      /** tag, always FUN */
      unsigned tag : 2;
      /** polarity, used only for literals */
      unsigned polarity : 1;
      /** true if commutative/symmetric */
      unsigned commutative : 1;
      /** true if shared */
      unsigned shared : 1;
      /** true if literal */
      unsigned literal : 1;
      /** true if atomic sort */
      unsigned sort : 1;
      /** Ordering comparison result for commutative term arguments, one of
       * 0 (unknown) 1 (less), 2 (equal), 3 (greater), 4 (incomparable)
       * @see Term::ArgumentOrder */
      unsigned order : 3;
      /** Number of distincs variables in the term, equal
       * to TERM_DIST_VAR_UNKNOWN if the number has not been
       * computed yet. */
      mutable unsigned distinctVars : 22;
      /** reserved for whatever */
#if ARCH_X64
      unsigned reserved : 32;
#endif
    } _info;
  };
  friend class Indexing::TermSharing;
  friend class Term;
  friend class Literal;
  friend class AtomicSort;
}; // class TermList

static_assert(
  sizeof(TermList) == sizeof(size_t),
  "size of TermList must be the same size as that of size_t"
);

/**
 * Class to represent terms and lists of terms.
 * @since 19/02/2008 Manchester, changed to use class TermList
 */
class Term
{
public:
  //special functor values
  static const unsigned SF_ITE = 0xFFFFFFFF;
  static const unsigned SF_LET = 0xFFFFFFFE;
  static const unsigned SF_FORMULA = 0xFFFFFFFD;
  static const unsigned SF_TUPLE = 0xFFFFFFFC;
  static const unsigned SF_LET_TUPLE = 0xFFFFFFFB;
  static const unsigned SF_LAMBDA = 0xFFFFFFFA;
  static const unsigned SF_MATCH = 0xFFFFFFF9;
  static const unsigned SPECIAL_FUNCTOR_LOWER_BOUND = 0xFFFFFFF9;

  class SpecialTermData
  {
    friend class Term;
  private:
    union {
      struct {
        Formula * condition;
        TermList sort;
      } _iteData;
      struct {
        unsigned functor;
        VList* variables;
	//The size_t stands for TermList expression which cannot be here
	//since C++ does not allow objects with constructor inside a union
  //Above comment doesn't hold in C++11
  //https://www.stroustrup.com/C++11FAQ.html#unions
        size_t binding;
        TermList sort;
      } _letData;
      struct {
        Formula * formula;
      } _formulaData;
      struct {
        Term* term;
      } _tupleData;
      struct {
        unsigned functor;
        VList* symbols;
        size_t binding;
        TermList sort;
      } _letTupleData;
      struct {
        TermList lambdaExp;
        VList* _vars;
        SList* _sorts;  
        TermList sort; 
        TermList expSort;//TODO is this needed?
      } _lambdaData;
      struct {
        TermList sort;
        TermList matchedSort;
      } _matchData;
    };
    /** Return pointer to the term to which this object is attached */
    const Term* getTerm() const { return reinterpret_cast<const Term*>(this+1); }
  public:
    unsigned getType() const {
      unsigned res = getTerm()->functor();
      ASS_GE(res,SPECIAL_FUNCTOR_LOWER_BOUND);
      return res;
    }
    Formula* getCondition() const { ASS_EQ(getType(), SF_ITE); return _iteData.condition; }
    unsigned getFunctor() const {
      ASS_REP(getType() == SF_LET || getType() == SF_LET_TUPLE, getType());
      return getType() == SF_LET ? _letData.functor : _letTupleData.functor;
    }
    VList* getLambdaVars() const { ASS_EQ(getType(), SF_LAMBDA); return _lambdaData._vars; }
    SList* getLambdaVarSorts() const { ASS_EQ(getType(), SF_LAMBDA); return _lambdaData._sorts; }
    TermList getLambdaExp() const { ASS_EQ(getType(), SF_LAMBDA); return _lambdaData.lambdaExp; }
    VList* getVariables() const { ASS_EQ(getType(), SF_LET); return _letData.variables; }
    VList* getTupleSymbols() const { return _letTupleData.symbols; }
    TermList getBinding() const {
      ASS_REP(getType() == SF_LET || getType() == SF_LET_TUPLE, getType());
      return TermList(getType() == SF_LET ? _letData.binding : _letTupleData.binding);
    }
    TermList getLambdaExpSort() const { ASS_EQ(getType(), SF_LAMBDA); return _lambdaData.expSort; }
    TermList getSort() const {
      switch (getType()) {
        case SF_ITE:
          return _iteData.sort;
        case SF_LET:
          return _letData.sort;
        case SF_LET_TUPLE:
          return _letTupleData.sort;
        case SF_LAMBDA:
          return _lambdaData.sort;
        case SF_MATCH:
          return _matchData.sort;
        default:
          ASSERTION_VIOLATION_REP(getType());
      }
    }
    Formula* getFormula() const { ASS_EQ(getType(), SF_FORMULA); return _formulaData.formula; }
    Term* getTupleTerm() const { return _tupleData.term; }
    TermList getMatchedSort() const { return _matchData.matchedSort; }
  };


  Term() throw();
  explicit Term(const Term& t) throw();
  static Term* create(unsigned function, unsigned arity, const TermList* args);
  static Term* create(unsigned fn, std::initializer_list<TermList> args);
  static Term* create(Term* t,TermList* args);
  static Term* createNonShared(unsigned function, unsigned arity, TermList* arg);
  static Term* createNonShared(Term* t,TermList* args);
  static Term* createNonShared(Term* t);
  static Term* cloneNonShared(Term* t);

  static Term* createConstant(const vstring& name);
  /** Create a new constant and insert in into the sharing structure */
  static Term* createConstant(unsigned symbolNumber) { return create(symbolNumber,0,0); }
  static Term* createITE(Formula * condition, TermList thenBranch, TermList elseBranch, TermList branchSort);
  static Term* createLet(unsigned functor, VList* variables, TermList binding, TermList body, TermList bodySort);
  static Term* createLambda(TermList lambdaExp, VList* vars, SList* sorts, TermList expSort);
  static Term* createTupleLet(unsigned functor, VList* symbols, TermList binding, TermList body, TermList bodySort);
  static Term* createFormula(Formula* formula);
  static Term* createTuple(unsigned arity, TermList* sorts, TermList* elements);
  static Term* createTuple(Term* tupleTerm);
  static Term* createMatch(TermList sort, TermList matchedSort, unsigned int arity, TermList* elements);
  static Term* create1(unsigned fn, TermList arg);
  static Term* create2(unsigned fn, TermList arg1, TermList arg2);

  //** fool constants
  static Term* foolTrue(); 
  static Term* foolFalse(); 

  VList* freeVariables() const;
  bool isFreeVariable(unsigned var) const;

  /** Return number of bytes before the start of the term that belong to it */
  size_t getPreDataSize() { return isSpecial() ? sizeof(SpecialTermData) : 0; }

  /** Function or predicate symbol of a term */
  const unsigned functor() const { return _functor; }

  vstring toString(bool topLevel = true) const;
  static vstring variableToString(unsigned var);
  static vstring variableToString(TermList var);

  /** return the arguments 
   *
   *  WARNING: this function returns a pointer to the first argument
   *  which could be a sort when dealing with a polymorphic problem!
   * 
   *  Use with care! Consider whether the termArgs() function may be more
   *  suited to your needs before using this.
   */
  const TermList* args() const
  { return _args + _arity; }
  /** return the nth argument (counting from 0) */
  const TermList* nthArgument(int n) const
  {
    ASS(n >= 0);
    ASS((unsigned)n < _arity);

    return _args + (_arity - n);
  }
  /** return the nth argument (counting from 0) */
  TermList* nthArgument(int n)
  {
    ASS(n >= 0);
    ASS((unsigned)n < _arity);

    return _args + (_arity - n);
  }

  /**
   * Return the number of type arguments for a polymorphic term (or 0 if monomorphic).
   */
  unsigned numTypeArguments() const;
  /**
   * Return the number of term arguments for a term (equal to _arity if monomorphic).
   */  
  unsigned numTermArguments() const;

  /** Return the 1st term argument for a polymorphic term.
    * Call hasTermArgs before calling this or test the result for
    * non-emptiness
    * In the monomorphic case, the same as args()
    */
  TermList* termArgs();

  /** Indexing operator for accessing arguments */
  const TermList operator[](int i) const {
    return *nthArgument(i);
  }
  TermList operator[](int i) {
    return *nthArgument(i);
  }

  /** return the arguments 
   *
   *  WARNING: this function returns a pointer to the first argument
   *  which could be a sort when dealing with a polymorphic problem!
   * 
   *  Use with care! Consider whether the termArgs() function may be more
   *  suited to your needs before using this.
   */  
  TermList* args()
  { return _args + _arity; }
  unsigned hash() const;
  /** return the arity */
  unsigned arity() const
  { return _arity; }
  static void* operator new(size_t,unsigned arity,size_t preData=0);
  /** make the term into a symbol term */
  void makeSymbol(unsigned number,unsigned arity)
  {
    _functor = number;
    _arity = arity;
  }
  void destroy();
  void destroyNonShared();
  Term* apply(Substitution& subst);

  /** True if the term is ground. Only applicable to shared terms */
  bool ground() const
  {
    ASS(_args[0]._info.shared);
    return ! vars();
  } // ground

  /** True if the term is shared */
  bool shared() const
  { return _args[0]._info.shared; } // shared

  /**
   * True if the term's function/predicate symbol is commutative/symmetric.
   * @pre the term must be complex
   */
  bool commutative() const
  {
    return _args[0]._info.commutative;
  } // commutative

  /** Return the weight. Applicable only to shared terms */
  unsigned weight() const
  {
    ASS(shared());
    return _weight;
  }

  int maxRedLength() const
  {
    ASS(shared());
    return _maxRedLen;    
  }

  /** Mark term as shared */
  void markShared()
  {
    ASS(! shared());
    _args[0]._info.shared = 1u;
  } // markShared

  /** Set term weight */
  void setWeight(unsigned w)
  {
    _weight = w;
  } // setWeight

  /** Set term id */
  void setId(unsigned id)
  {
    _id = id;
  } // setWeight

  /** Set (shared) term's id */
  unsigned getId() const
  {
    ASS(shared());
    return _id;
  }
  
  void setMaxRedLen(int rl)
  {
    _maxRedLen = rl;
  } // setWeight

  /** Set the number of variables */
  void setVars(unsigned v)
  {
    CALL("Term::setVars");

    if(_isTwoVarEquality) {
      ASS_EQ(v,2);
      return;
    }
    _vars = v;
  } // setVars

  /** Return the number of variables */
  unsigned vars() const
  {
    ASS(shared());
    if(_isTwoVarEquality) {
      return _sort.isVar() ? 3 : 2 + _sort.term()->vars(); 
    }
    return _vars;
  } // vars()

  /**
   * Return true iff the object is an equality between two variables.
   *
   * This value is set during insertion into the term sharing structure or
   * for terms with special subterms during construction.
   * (I.e. can be used basically anywhere).
   */
  bool isTwoVarEquality() const
  {
    return _isTwoVarEquality;
  }

  const vstring& functionName() const;

  /** True if the term is, in fact, a literal */
  bool isLiteral() const { return _args[0]._info.literal; }

  void reverseOrientation()
  {
    _orientation ^= 1;
  }

  void resetOrientation()
  {
    _orientation = 0;
  }

  bool isOrientedReversed()
  {
    return _orientation;
  }
  
  /** True if the term is, in fact, a sort */
  bool isSort() const { return _args[0]._info.sort; }
  /** true if the term is an application */
  bool isApplication() const;

  /** Return an index of the argument to which @b arg points */
  unsigned getArgumentIndex(TermList* arg)
  {
    CALL("Term::getArgumentIndex");

    unsigned res=arity()-(arg-_args);
    ASS_L(res,arity());
    return res;
  }

#if VDEBUG
  vstring headerToString() const;
  void assertValid() const;
#endif


  static TermIterator getVariableIterator(TermList tl);

//  static Comparison lexicographicCompare(TermList t1, TermList t2);
//  static Comparison lexicographicCompare(Term* t1, Term* t2);

  /** If number of distinct variables is computed, assign it to res and
   * return true, otherwise return false. */
  bool askDistinctVars(unsigned& res) const
  {
    if(_args[0]._info.distinctVars==TERM_DIST_VAR_UNKNOWN) {
      return false;
    }
    res=_args[0]._info.distinctVars;
    return true;
  }
  unsigned getDistinctVars() const
  {
    if(_args[0]._info.distinctVars==TERM_DIST_VAR_UNKNOWN) {
      unsigned res=computeDistinctVars();
      if(res<TERM_DIST_VAR_UNKNOWN) {
	_args[0]._info.distinctVars=res;
      }
      return res;
    } else {
      ASS_L(_args[0]._info.distinctVars,0x100000);
      return _args[0]._info.distinctVars;
    }
  }

  bool couldBeInstanceOf(Term* t)
  {
    ASS(shared());
    ASS(t->shared());
    if(t->functor()!=functor()) {
      return false;
    }
    ASS(!commutative());
    return true;
  }

  bool containsSubterm(TermList v);
  bool containsAllVariablesOf(Term* t);
  size_t countSubtermOccurrences(TermList subterm);

  /** Return true if term has no non-constant functions as subterms */
  bool isShallow() const;

  /** set the colour of the term */
  void setColor(Color color)
  {
    ASS(_color == static_cast<unsigned>(COLOR_TRANSPARENT) || _color == static_cast<unsigned>(color));
    _color = color;
  } // setColor
  /** return the colour of the term */
  Color color() const { return static_cast<Color>(_color); }

  bool skip() const;

  /** Return true if term is an interpreted constant or contains one as its subterm */
  bool hasInterpretedConstants() const { return _hasInterpretedConstants; }
  /** Assign value that will be returned by the hasInterpretedConstants() function */
  void setInterpretedConstantsPresence(bool value) { _hasInterpretedConstants=value; }

  /** Return true if term is either an if-then-else or a let...in expression */
  bool isSpecial() const { return functor()>=SPECIAL_FUNCTOR_LOWER_BOUND; }
  bool isITE() const { return functor() == SF_ITE; }
  bool isLet() const { return functor() == SF_LET; }
  bool isTupleLet() const { return functor() == SF_LET_TUPLE; }
  bool isTuple() const { return functor() == SF_TUPLE; }
  bool isFormula() const { return functor() == SF_FORMULA; }
  bool isLambda() const { return functor() == SF_LAMBDA; }
  bool isMatch() const { return functor() == SF_MATCH; }
  bool isBoolean() const;
  bool isSuper() const; 
  
  /** Return pointer to structure containing extra data for special terms such as
   * if-then-else or let...in */
  const SpecialTermData* getSpecialData() const { return const_cast<Term*>(this)->getSpecialData(); }
  /** Return pointer to structure containing extra data for special terms such as
   * if-then-else or let...in */
  SpecialTermData* getSpecialData() {
    CALL("Term::getSpecialData");
    ASS(isSpecial());
    return reinterpret_cast<SpecialTermData*>(this)-1;
  }
protected:
  vstring headToString() const;

  unsigned computeDistinctVars() const;

  /**
   * Return argument order value stored in term.
   *
   * The default value (which is returned if no value was set using the
   * @c setArgumentOrder() function) is zero.
   *
   * Currently, this function is used only by @c Ordering::getEqualityArgumentOrder().
   */
  int getArgumentOrderValue() const
  {
    return _args[0]._info.order;
  }

  /**
   * Store argument order value in term.
   *
   * The value must be non-negative and less than 8.
   *
   * Currently, this function is used only by @c Ordering::getEqualityArgumentOrder().
   */
  void setArgumentOrderValue(int val)
  {
    CALL("Term::setArgumentOrderValue");
    ASS_GE(val,0);
    ASS_L(val,8);

    _args[0]._info.order = val;
  }

  /** For shared terms, this is a unique id used for deterministic comparison */
  unsigned _id;
  /** The number of this symbol in a signature */
  unsigned _functor;
  /** Arity of the symbol */
  unsigned _arity : 27;
  /** colour, used in interpolation and symbol elimination */
  unsigned _color : 2;
  /** Equal to 1 if the term/literal contains any interpreted constants */
  unsigned _hasInterpretedConstants : 1;
  /** If true, the object is an equality literal between two variables */
  unsigned _isTwoVarEquality : 1;
  /** Weight of the symbol */
  unsigned _weight;
  /** If true, the literal is oriented reversed compared to the initial orientation */
  unsigned _orientation : 1;
  /** length of maximum reduction length */
  int _maxRedLen;
  union {
    /** If _isTwoVarEquality is false, this value is valid and contains
     * number of occurrences of variables */
    unsigned _vars;
    /** If _isTwoVarEquality is true, this value is valid and contains
     * the sort of the top-level variables */
    TermList _sort;
  };

  /** The list of arguments of size type arity + term arity + 1. The first
   *  argument stores the term weight and the mask (the last two bits are 0).
   */
  TermList _args[1];


//   /** set all boolean fields to false and weight to 0 */
//   void initialise()
//   {
//     shared = 0;
//       ground = 0;
//       weight = 0;
//     }
//   };

//   Comparison compare(const Term* t) const;
//   void argsWeight(unsigned& total) const;
  friend class TermList;
  friend class Indexing::TermSharing;
  friend class Ordering;

public:
  /**
   * Iterator returning arguments of a term left-to-right.
   */
  class Iterator
  {
  public:
    DECL_ELEMENT_TYPE(TermList);
    Iterator(Term* t) : _next(t->args()) {}
    bool hasNext() const { return _next->isNonEmpty(); }
    TermList next()
    {
      CALL("Term::Iterator::next");
      ASS(hasNext());
      TermList res = *_next;
      _next = _next->next();
      return res;
    }
  private:
    TermList* _next;
  }; // Term::Iterator
}; // class Term


/**
 * Class of AtomicSort.
 */
class AtomicSort
  : public Term
{
public:
  AtomicSort();
  explicit AtomicSort(const AtomicSort& t) throw();

  AtomicSort(unsigned functor,unsigned arity) throw()
  {
    _functor = functor;
    _arity = arity;
    _args[0]._info.literal = 0u;
    _args[0]._info.sort = 1u;
  }

  static AtomicSort* create(unsigned typeCon, unsigned arity, const TermList* args);
  static AtomicSort* create2(unsigned tc, TermList arg1, TermList arg2);
  static AtomicSort* create(AtomicSort* t,TermList* args);
  static AtomicSort* createConstant(unsigned typeCon) { return create(typeCon,0,0); }
  static AtomicSort* createConstant(const vstring& name); 

  /** True if the sort is a higher-order arrow sort */
  bool isArrowSort() const;
  /** True if the sort $o */
  bool isBoolSort() const;
  /** true if sort is the sort of an array */
  bool isArraySort() const;
  /** true if sort is the sort of an tuple */
  bool isTupleSort() const;

  const vstring& typeConName() const;  
  
  static TermList arrowSort(TermStack& domSorts, TermList range);
  static TermList arrowSort(TermList s1, TermList s2);
  static TermList arrowSort(TermList s1, TermList s2, TermList s3);
  static TermList arraySort(TermList indexSort, TermList innerSort);
  static TermList tupleSort(unsigned arity, TermList* sorts);
  static TermList defaultSort();
  static TermList superSort();
  static TermList boolSort();
  static TermList intSort();
  static TermList realSort();
  static TermList rationalSort();

private:

  static AtomicSort* createNonShared(unsigned typeCon, unsigned arity, TermList* arg);
  static AtomicSort* createNonSharedConstant(unsigned typeCon) { return createNonShared(typeCon,0,0); }
};

/**
 * Class of literals.
 * @since 06/05/2007 Manchester
 */
class Literal
  : public Term
{
public:
  /** True if equality literal */
  bool isEquality() const
  { return functor() == 0; }

  Literal();
  explicit Literal(const Literal& l) throw();

  /**
   * Create a literal.
   * @since 16/05/2007 Manchester
   */
  Literal(unsigned functor,unsigned arity,bool polarity,bool commutative) throw()
  {
    _functor = functor;
    _arity = arity;
    _args[0]._info.polarity = polarity;
    _args[0]._info.commutative = commutative;
    _args[0]._info.sort = 0u;
    _args[0]._info.literal = 1u;
  }

  /**
   * A unique header, 2*p is negative and 2*p+1 if positive where p is
   * the number of the predicate symbol.
   */
  unsigned header() const
  { return 2*_functor + polarity(); }
  /**
   * Header of the complementary literal, 2*p+1 is negative and 2*p
   * if positive where p is the number of the predicate symbol.
   */
  unsigned complementaryHeader() const
  { return 2*_functor + 1 - polarity(); }

  /**
   * Convert header to the correponding predicate symbol number.
   * @since 08/08/2008 flight Manchester-Singapore
   */
  static unsigned int headerToPredicateNumber(unsigned header)
  {
    return header/2;
  }
  /**
   * Convert header to the correponding polarity.
   * @since 08/08/2008 flight Manchester-Singapore
   */
  static unsigned int headerToPolarity(unsigned header)
  {
    return header % 2;
  }
  static bool headersMatch(Literal* l1, Literal* l2, bool complementary);
  /** Negate, should not be used with shared terms */
  void negate()
  {
    ASS(! shared());
    _args[0]._info.polarity = 1 - _args[0]._info.polarity;
  }
  /** set polarity to true or false */
  void setPolarity(bool positive)
  { _args[0]._info.polarity = positive ? 1 : 0; }
  static Literal* create(unsigned predicate, unsigned arity, bool polarity,
	  bool commutative, const TermList* args);
  static Literal* create(Literal* l,bool polarity);
  static Literal* create(Literal* l,TermList* args);
  static Literal* createEquality(bool polarity, TermList arg1, TermList arg2, TermList sort);
  static Literal* create1(unsigned predicate, bool polarity, TermList arg);
  static Literal* create2(unsigned predicate, bool polarity, TermList arg1, TermList arg2);
  static Literal* create(unsigned fn, bool polarity, std::initializer_list<TermList> args);

  //No longer used AYB
  //static Literal* flattenOnArgument(const Literal*,int argumentNumber);

  unsigned hash() const;
  unsigned oppositeHash() const;
  static Literal* complementaryLiteral(Literal* l);
  /** If l is positive, return l; otherwise return its complementary literal. */
  static Literal* positiveLiteral(Literal* l) {
    return l->isPositive() ? l : complementaryLiteral(l);
  }
  /** If l is negative, return l; otherwise return its complementary literal. */
  static Literal* negativeLiteral(Literal* l) {
    return l->isNegative() ? l : complementaryLiteral(l);
  }

  /** true if positive */
  bool isPositive() const
  {
    return _args[0]._info.polarity;
  } // isPositive

  /** true if negative */
  bool isNegative() const
  {
    return ! _args[0]._info.polarity;
  } // isNegative

  /** return polarity, 1 if positive and 0 if negative */
  int polarity() const
  {
    return _args[0]._info.polarity;
  } // polarity

  /**
   * Mark this object as an equality between two variables.
   */
  void markTwoVarEquality()
  {
    CALL("Literal::markTwoVarEquality");
    ASS(!shared());
    ASS(isEquality());
    ASS(nthArgument(0)->isVar() || !nthArgument(0)->term()->shared());
    ASS(nthArgument(1)->isVar() || !nthArgument(1)->term()->shared());

    _isTwoVarEquality = true;
  }


  /** Return sort of the variables in an equality between two variables.
   * This value is set during insertion into the term sharing structure
   */
  TermList twoVarEqSort() const
  {
    CALL("Literal::twoVarEqSort");
    ASS(isTwoVarEquality());

    return _sort;
  }

  /** Assign sort of the variables in an equality between two variables. */
  void setTwoVarEqSort(TermList sort)
  {
    CALL("Literal::setTwoVarEqSort");
    ASS(isTwoVarEquality());

    _sort = sort;
  }


  /** Return a new equality literal */
  static inline Literal* equality (bool polarity)
  {
     CALL("Literal::equality/1");
     return new(2) Literal(0,2,polarity,true);
  }

//   /** Applied @b subst to the literal and return the result */
  Literal* apply(Substitution& subst);


  inline bool couldBeInstanceOf(Literal* lit, bool complementary)
  {
    ASS(shared());
    ASS(lit->shared());
    return headersMatch(this, lit, complementary);
  }

  vstring toString() const;
  const vstring& predicateName() const;

private:
  static Literal* createVariableEquality(bool polarity, TermList arg1, TermList arg2, TermList variableSort);

}; // class Literal

// TODO used in some proofExtra output
//      find a better place for this?
bool positionIn(TermList& subterm,TermList* term, vstring& position);
bool positionIn(TermList& subterm,Term* term, vstring& position);

struct TermListHash {
  static unsigned hash(TermList t) {
    return static_cast<unsigned>(t.content());
  }
};

std::ostream& operator<< (ostream& out, TermList tl );
std::ostream& operator<< (ostream& out, const Term& tl );
std::ostream& operator<< (ostream& out, const Literal& tl );

};

/* template specializations */
namespace Lib
{


template<>
struct FirstHashTypeInfo<Kernel::TermList> {
  typedef Kernel::TermListHash Type;
};


}

#endif
