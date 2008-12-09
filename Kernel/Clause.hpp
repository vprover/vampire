/**
 * @file Clause.hpp
 * Defines class Clause for units consisting of clauses
 *
 * @since 09/05/2007 Manchester
 */

#ifndef __Clause__

#include "../Forwards.hpp"
#include "../Lib/Allocator.hpp"

#include "Unit.hpp"

using namespace Lib;

namespace Kernel {


/**
 * Class to represent clauses.
 * @since 10/05/2007 Manchester
 */
class Clause
  : public Unit
{
public:
  /** Storage kind */
  enum Store {
    /** passive clause */
    PASSIVE = 0u,
    /** active clause */
    ACTIVE = 1u,
    /** queue of unprocessed clauses */
    UNPROCESSED = 2u,
    /** anything else */
    NONE = 3u
  };

  /** New unit of a given kind */
  Clause(unsigned length,InputType it,Inference* inf)
    : Unit(Unit::CLAUSE,inf,it),
      _length(length),
      _weight(0),
      _store(NONE),
      _inferenceRefCnt(0)
  {}

  /** Should never be used, declared just to get rid of compiler warning */
  virtual ~Clause() { ASSERTION_VIOLATION; }

  void* operator new(size_t,unsigned length);

  /** Return the (reference to) the nth literal */
  Literal*& operator[] (int n)
  { return _literals[n]; }
  /** Return the (reference to) the nth literal */
  const Literal*& operator[] (int n) const
  { return const_cast<const Literal*&>(_literals[n]); }

  /** Return the length (number of literals) */
  unsigned length() const { return _length; }

  /** Return a pointer to the array of literals. Note that the
   * caller of this function may directly manipulate literals, for
   * example reorder them */
  Literal** literals() { return _literals; }

  /** True if the clause is empty */
  bool isEmpty() const { return _length == 0; }

  void destroy();
  string toString() const;

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
  { ASS(s >= 0);
    ASS(s <= _length);
    _selected = s; }

  /** Return the weight */
  int weight() const { return _weight; }
  void computeWeight();

  /** If storage is set to NONE and there are no references to this class, destroy it. */
  void destroyIfUnnecessary()
  { if(_store==NONE && _inferenceRefCnt==0) { destroy(); } }

  void incRefCnt() { _inferenceRefCnt++; }
  void decRefCnt() { _inferenceRefCnt--; destroyIfUnnecessary(); }

#if VDEBUG
  bool contains(Literal* lit);
#endif
protected:
  /** number of literals */
  unsigned _length;
  /** number of selected literals */
  unsigned _selected;
  /** age */
  unsigned _age;
  /** weight */
  unsigned _weight;
  /** storage class */
  Store _store;
  /** number of references to this clause by inference rules */
  unsigned _inferenceRefCnt;
  /** Array of literals of this unit */
  Literal* _literals[1];
}; // class Clause

}
#endif
