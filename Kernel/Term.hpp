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
#include <string>

#include "../Forwards.hpp"
#include "../Debug/Assertion.hpp"
#include "../Debug/Tracer.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/Portability.hpp"
#include "../Lib/XML.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/Stack.hpp"

#if VDEBUG

#include <iosfwd>

#endif

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

/**
 * Class containing either a pointer to a compound term or
 * a variable number or a functor.
 */
class TermList {
public:
  /** the tag */
  TermTag tag() const { return (TermTag)(_content & 0x0003); }
  /** the term list is empty */
  bool isEmpty() const
  { return tag() == FUN; }
  /** the term list is non-empty */
  bool isNonEmpty() const
  { return tag() != FUN; }
  /** next term in this list */
  TermList* next()
  { return this-1; }
  /** next term in this list */
  const TermList* next() const
  { return this-1; }
  /** the term contains a variable as its head */
  bool isVar() const { return (_content & 0x0001) == 1; }
  /** the term contains an ordinary variable as its head */
  bool isOrdinaryVar() const { return tag() == ORD_VAR; }
  /** the term contains a special variable as its head */
  bool isSpecialVar() const { return tag() == SPEC_VAR; }
  /** return the variable number */
  unsigned var() const
  { ASS(isVar()); return _content / 4; }
  /** the term contains reference to Term class */
  bool isTerm() const
  { return tag() == REF; }
  const Term* term() const
  { return _term; }
  Term* term()
  { return _term; }
  /** True of the terms have the same content. Useful for comparing
   * arguments of shared terms. */
  bool sameContent(const TermList* t) const
  { return _content == t->_content ; }
  /** return the content, useful for e.g., term argument comparison */
  size_t content() const { return _content; }
  string toString() const;
  /** make the term into an ordinary variable with a given number */
  void makeVar(unsigned vnumber)
  { _content = vnumber * 4 + ORD_VAR; }
  /** make the term into a special variable with a given number */
  void makeSpecialVar(unsigned vnumber)
  { _content = vnumber * 4 + SPEC_VAR; }
  /** make the term empty (so that isEmpty() returns true) */
  void makeEmpty()
  { _content = FUN; }
  /** make the term into a reference */
  void setTerm(Term* t)
  { _term = t; }
  static void argsToString(Stack<const TermList*>&,string& str);
  static bool sameTop(const TermList* ss,const TermList* tt);
  static bool sameTopFunctor(const TermList* ss,const TermList* tt);
  static bool equals(TermList t1, TermList t2);

#if VDEBUG
  void assertValid() const;
#endif

  bool operator==(const TermList& t) const
  { return _content==t._content; }
  bool operator!=(const TermList& t) const
  { return _content!=t._content; }
  bool operator<(const TermList& t) const
  { return _content<t._content; }
  bool operator>(const TermList& t) const
  { return _content>t._content; }

private:
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
      /** Ordering comparison result for commutative term arguments, one of
       * 0 (unknown) 1 (less), 2 (equal), 3 (greater), 4 (incomparable) */
      unsigned order : 3;
      /** reserved for whatever */
#ifdef ARCH_X64
      size_t reserved : 55;
#else
      unsigned reserved : 23;
#endif
    } _info;
  };
  friend class Indexing::TermSharing;
  friend class Term;
  friend class Literal;
}; // class TermList

/**
 * Class to represent terms and lists of terms.
 * @since 19/02/2008 Manchester, changed to use class TermList
 */
class Term
{
public:
  Term();
  explicit Term(const Term& t);
  void orderArguments();
  static Term* create(Term* t,TermList* args);
  static Term* createNonShared(Term* t,TermList* args);
  static Term* createNonShared(Term* t);
  static Term* cloneNonShared(Term* t);
  /** Function or predicate symbol of a term */
  const unsigned functor() const
  {
    return _functor;
  }

  static XMLElement variableToXML(unsigned var);
  string toString() const;
  static string variableToString(unsigned var);
  /** return the arguments */
  const TermList* args() const
  { return _args + _arity; }
  /** return the nth argument (counting from 0) */
  const TermList* nthArgument(int n) const
  {
    ASS(n >= 0);
    ASS((unsigned)n < _arity);

    return _args + (_arity - n);
  }
  /** return the arguments */
  TermList* args()
  { return _args + _arity; }
  unsigned hash() const;
  /** return the arity */
  unsigned arity() const
  { return _arity; }
  static void* operator new(size_t,unsigned arity);
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
    return ! _vars;
  } // ground

  /** True if the term is shared */
  bool shared() const
  { return _args[0]._info.shared; } // shared

  /**
   * True if the term's function/predicate symbol is commutative/symmetric.
   * @pre the term must be complex
   */
  bool commutative()
  {
    return _args[0]._info.commutative;
  } // commutative

  /** Return the weight. Applicable only to shared terms */
  unsigned weight() const
  {
    ASS(shared());
    return _weight;
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

  /** Set the number of variables */
  void setVars(unsigned v)
  {
    _vars = v;
  } // setVars

  /** Return the number of variables */
  unsigned vars() const
  {
    ASS(_args[0]._info.shared);
    return _vars;
  } // vars()

  const string& functionName() const;

  /** True if the term is, in fact, a literal */
  bool isLiteral() const { return _args[0]._info.literal; }

#if VDEBUG
  string headerToString() const;
  void assertValid() const;
#endif

  class VariableIterator {
  public:
    DECL_ELEMENT_TYPE(TermList);
    VariableIterator(const Term* term) : _stack(8), _used(false)
    {
      if(!term->shared() || !term->ground()) {
	_stack.push(term->args());
      }
    }

    bool hasNext();
    /** Return the next variable
     * @warning hasNext() must have been called before */
    TermList next()
    {
      ASS(!_used && _stack.top()->isVar());
      _used=true;
      return *_stack.top();
    }
  private:
    Stack<const TermList*> _stack;
    bool _used;
  };

  /**
   * Iterator that yields non-variable proper subterms
   * of specified @b term.
   */
  class NonVariableIterator {
  public:
    DECL_ELEMENT_TYPE(TermList);
    NonVariableIterator(const Term* term) : _stack(8), _used(false)
    {
      pushNextNonVar(term->args());
    }

    bool hasNext();
    /** Return the next variable
     * @warning hasNext() must have been called before */
    TermList next()
    {
      ASS(!_used && !_stack.top()->isVar());
      _used=true;
      return *_stack.top();
    }
  private:
    inline
    void pushNextNonVar(const TermList* t)
    {
      while(t->isVar()) {
        t=t->next();
      }
      if(!t->isEmpty()) {
	ASS(t->isTerm());
	_stack.push(t);
      }
    }
    Stack<const TermList*> _stack;
    bool _used;
  };

protected:
  /** The number of this symbol in a signature */
  unsigned _functor;
  /** Arity of the symbol */
  unsigned _arity;
  /** Weight of the symbol */
  unsigned _weight;
  /** number of occurrences of variables */
  unsigned _vars;

  /** The list of arguments or size arity+1. The first argument stores the
   *  term weight and the mask (the last two bits are 0).
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
}; // class Term

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

  explicit Literal(const Literal& l);

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
  static bool headersMatch(Literal* l1, Literal* l2, bool complementary)
  {
    return l1->_functor==l2->_functor &&
      (complementary?1:0)==(l1->polarity()^l2->polarity());
  }
  /** Negate, should not be used with shared terms */
  void negate()
  {
    ASS(! shared());
    _args[0]._info.polarity = 1 - _args[0]._info.polarity;
  }
  /** set polarity to true or false */
  void setPolarity(bool positive)
  { _args[0]._info.polarity = positive ? 1 : 0; }
  static Literal* create(Literal* l,TermList* args);

  static Literal* flattenOnArgument(const Literal*,int argumentNumber);

  /**
   * Create a literal.
   * @since 16/05/2007 Manchester
   */
  Literal(unsigned functor,unsigned arity,bool polarity,bool commutative)
  {
    _functor = functor;
    _arity = arity;
    _args[0]._info.polarity = polarity;
    _args[0]._info.commutative = commutative;
    _args[0]._info.literal = 1u;
  }

  unsigned hash() const;
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

  /** Return a new equality literal */
  static inline Literal* equality (bool polarity)
  {
     CALL("Literal::equality");
     return new(2) Literal(0,2,polarity,true);
  }

//   /** Applied @b subst to the literal and return the result */
  Literal* apply(Substitution& subst);

//   XMLElement toXML() const;
  string toString() const;
  const string& predicateName() const;
}; // class Literal


#if VDEBUG

std::ostream& operator<< (ostream& out, TermList tl );
std::ostream& operator<< (ostream& out, const Term& tl );
std::ostream& operator<< (ostream& out, const Literal& tl );

#endif

}
#endif
