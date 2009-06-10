/**
 * @file Clause.hpp
 * Defines class Clause for units consisting of clauses
 *
 * @since 09/05/2007 Manchester
 */

#ifndef __Clause__
#define __Clause__

#include <iosfwd>

#include "../Forwards.hpp"
#include "../Lib/Allocator.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Reflection.hpp"
#include "../Lib/InverseLookup.hpp"

#include "Unit.hpp"


namespace Kernel {

using namespace Lib;

/**
 * Class to represent clauses.
 * @since 10/05/2007 Manchester
 */
class Clause
  : public Unit
{
public:
  DECL_ELEMENT_TYPE(Literal*);
  DECL_ITERATOR_TYPE(ArrayishObjectIterator<Clause>);

  /** Storage kind */
  enum Store {
    /** passive clause */
    PASSIVE = 0u,
    /** active clause */
    ACTIVE = 1u,
    /** queue of unprocessed clauses */
    UNPROCESSED = 2u,
    /** anything else */
    NONE = 3u,
    /**
     * Active clause (it is in appropriate indexes) that is put to
     * passive queue for another activation.
     *
     * This is intended for clauses whose propositional part has
     * changed.
     */
    REACTIVATED = 5u
  };

  /** New unit of a given kind */
  Clause(unsigned length,InputType it,Inference* inf)
    : Unit(Unit::CLAUSE,inf,it),
      _length(length),
      _selected(0),
      _age(0),
      _weight(0),
      _store(NONE),
      _inferenceRefCnt(0),
      _literalPositions(0),
      _prop(0),
      _auxTimestamp(0)
  {}

  /** Should never be used, declared just to get rid of compiler warning */
  virtual ~Clause() { ASSERTION_VIOLATION; }

  void* operator new(size_t,unsigned length);

  /**
   * Return the (reference to) the nth literal
   *
   * Positions of literals in the clause are cached in the _literalPositions
   * object. In order to keep it in sync, content of the clause can be changed
   * only right after clause construction (before the first call to the
   * getLiteralPosition method), or during the literal selection (as the
   * _literalPositions object is updated in call to the setSelected method).
   */
  Literal*& operator[] (int n)
  { return _literals[n]; }
  /** Return the (reference to) the nth literal */
  const Literal*& operator[] (int n) const
  { return const_cast<const Literal*&>(_literals[n]); }

  /** Return the length (number of literals) */
  unsigned length() const { return _length; }
  /** Alternative name for length to conform with other containers */
  unsigned size() const { return _length; }

  /** Return a pointer to the array of literals.
   * Caller should not malipulate literals, with the exception of
   * clause construction and literal selection. */
  Literal** literals() { return _literals; }

  /** True if the clause is empty */
  bool isEmpty() const { return _length == 0; }

  void destroy();
  void destroyExceptInferenceObject();
  string nonPropToString() const;
  string toString() const;
  string toString(BDDNode* propPart) const;

  /** Return the clause store */
  Store store() const { return _store; }
  /** Set the store to @b s */
  void setStore(Store s) { _store = s; destroyIfUnnecessary(); }

  /** Return the age */
  int age() const { return _age; }
  /** Set the age to @b a */
  void setAge(int a) { _age = a; }

  /** Return the number of selected literals */
  unsigned selected() const { return _selected; }
  /** Mark the first s literals as selected */
  void setSelected(unsigned s)
  {
    ASS(s >= 0);
    ASS(s <= _length);
    _selected = s;
    if(_literalPositions) {
      _literalPositions->update(_literals);
    }
  }

  /** Return the weight */
  int weight() const
  {
    if(!_weight) {
      computeWeight();
    }
    return _weight;
  }
  void computeWeight() const;

  unsigned getLiteralPosition(Literal* lit)
  {
    if(!_literalPositions) {
      _literalPositions=new InverseLookup<Literal>(_literals,length());
    }
    return static_cast<unsigned>(_literalPositions->get(lit));
  }

  bool shouldBeDestroyed();
  void destroyIfUnnecessary();

  void incRefCnt() { _inferenceRefCnt++; }
  void decRefCnt() { _inferenceRefCnt--; destroyIfUnnecessary(); }

  ArrayishObjectIterator<Clause> getSelectedLiteralIterator()
  { return ArrayishObjectIterator<Clause>(*this,selected()); }

#if VDEBUG
  bool contains(Literal* lit);
  void assertValid();
#endif

  /** Return the propositional part of the clause */
  BDDNode* prop() const { return _prop; }

  void setProp(BDDNode* prop);

  /** Set auxiliary value of this clause. */
  void setAux(void* ptr)
  {
    ASS(_auxInUse);
    _auxTimestamp=_auxCurrTimestamp;
    _auxData=ptr;
  }
  /**
   * If there is an auxiliary value stored in this clause,
   * return true and assign it into @b ptr. Otherwise
   * return false.
   */
  template<typename T>
  bool tryGetAux(T*& ptr)
  {
    ASS(_auxInUse);
    if(_auxTimestamp==_auxCurrTimestamp) {
      ptr=static_cast<T*>(_auxData);
      return true;
    }
    return false;
  }
  /** Return auxiliary value stored in this clause. */
  template<typename T>
  T* getAux()
  {
    ASS(_auxInUse);
    ASS(_auxTimestamp==_auxCurrTimestamp);
    return static_cast<T*>(_auxData);
  }
  bool hasAux()
  {
    return _auxTimestamp==_auxCurrTimestamp;
  }

  /**
   * Request usage of the auxiliary value in clauses.
   * All aux. values stored in clauses before are guaranteed
   * to be discarded.
   */
  static void requestAux()
  {
#if VDEBUG
    ASS(!_auxInUse);
    _auxInUse=true;
#endif
    _auxCurrTimestamp++;
  }
  /**
   * Announce that the auxiliary value in clauses is no longer
   * in use and can be used by someone else.
   */
  static void releaseAux()
  {
#if VDEBUG
    ASS(_auxInUse);
    _auxInUse=false;
#endif
  }

  float getEffectiveWeight(unsigned originalWeight);
  float getEffectiveWeight();
protected:
  /** number of literals */
  unsigned _length;
  /** number of selected literals */
  unsigned _selected;
  /** age */
  unsigned _age;
  /** weight */
  mutable unsigned _weight;
  /** storage class */
  Store _store;
  /** number of references to this clause by inference rules */
  unsigned _inferenceRefCnt;
  /** a map that translates Literal* to its index in the clause */
  InverseLookup<Literal>* _literalPositions;

  /** propositional part of the Clause */
  BDDNode* _prop;

  size_t _auxTimestamp;
  void* _auxData;

  static size_t _auxCurrTimestamp;
#if VDEBUG
  static bool _auxInUse;
#endif

  /** Array of literals of this unit */
  Literal* _literals[1];
}; // class Clause

std::ostream& operator<< (ostream& out, const Clause& cl );

}

#endif
