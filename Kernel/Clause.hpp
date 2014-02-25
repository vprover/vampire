/**
 * @file Clause.hpp
 * Defines class Clause for units consisting of clauses
 *
 * @since 09/05/2007 Manchester
 */

#ifndef __Clause__
#define __Clause__

#include <iosfwd>

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Event.hpp"
#include "Lib/InverseLookup.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/Stack.hpp"

#include "Unit.hpp"


namespace Kernel {

using namespace Lib;

/**
 * Class to represent clauses.
 * @since 10/05/2007 Manchester
 *
 * When creating a clause object, several things usually need to be done
 * besides calling a constructor:
 * - Fill the Clause with Literals
 * - Increase a relevant counter in the env.statistics object
 * - Set Clause's age if it is not supposed to be zero
 * - Assign Clause's non-propositional part if Clause appears in the
 *   SaturationAlgorithm loop
 * 	- should be done by the SaturationAlgorithm object
 *   Giles. no longer do this - no prop part.
 *
 * - Register Clause's inference in the InferenceStore by
 *   @code InferenceStore::instance()->recordNonPropInference(clause); @endcode
 * 	- should be done by the SaturationAlgorithm object
 *   Giles. no longer do this - this was only required when clauses had
 *   propositional parts.
 *
 */
class Clause
  : public Unit
{
private:
  /** Should never be used, declared just to get rid of compiler warning */
  ~Clause() { ASSERTION_VIOLATION; }
  /** Should never be used, just that compiler requires it */
  void operator delete(void* ptr) { ASSERTION_VIOLATION; }
public:
  typedef ArrayishObjectIterator<Clause> Iterator;

  DECL_ELEMENT_TYPE(Literal*);
  DECL_ITERATOR_TYPE(Iterator);

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
    /** clause removed by backtracking splitting */
    BACKTRACKED = 4u,
    /** clause is selected from the passive container
     * and is not added to the active one yet */
    SELECTED = 5u
  };

  Clause(unsigned length,InputType it,Inference* inf);


  void* operator new(size_t,unsigned length);
  void operator delete(void* ptr,unsigned length);

  static Clause* fromStack(const Stack<Literal*>& lits, InputType it, Inference* inf);

  template<class Iter>
  static Clause* fromIterator(Iter litit, InputType it, Inference* inf)
  {
    CALL("Clause::fromIterator");

    static Stack<Literal*> st;
    st.reset();
    st.loadFromIterator(litit);
    return fromStack(st, it, inf);
  }

  static Clause* fromClause(Clause* c);

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
  Literal* operator[] (int n) const
  { return _literals[n]; }

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
  string toTPTPString() const;
  string toNiceString() const;

  /** Return the clause store */
  Store store() const { return _store; }

  void setStore(Store s);

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
    notifyLiteralReorder();
  }

  /** Return whether this clause is in the active index **/
  bool in_active() const {return _in_active;}
  /** Set _in_active to false if true and vice versa **/
  void toggle_in_active() {_in_active=!_in_active;}

  /** Return the weight */
  int weight() const
  {
    if(!_weight) {
      computeWeight();
    }
    return _weight;
  }
  void computeWeight() const;

  /** Return the color of a clause */
  Color color() const
  {
    if(static_cast<Color>(_color)==COLOR_INVALID) {
      computeColor();
    }
    return static_cast<Color>(_color);
  }
  void computeColor() const;

  bool skip() const;

  unsigned getLiteralPosition(Literal* lit);
  void notifyLiteralReorder();

  bool shouldBeDestroyed();
  void destroyIfUnnecessary();

  void incRefCnt() { _inferenceRefCnt++; }
  void decRefCnt()
  {
    CALL("Clause::decRefCnt");

    ASS_G(_inferenceRefCnt,0);
    _inferenceRefCnt--;
    destroyIfUnnecessary();
  }

  unsigned getReductionTimestamp() { return _reductionTimestamp; }
  void incReductionTimestamp()
  {
    _reductionTimestamp++;
    if(_reductionTimestamp==0) {
      INVALID_OPERATION("Clause reduction timestamp overflow!");
    }
  }

  ArrayishObjectIterator<Clause> getSelectedLiteralIterator()
  { return ArrayishObjectIterator<Clause>(*this,selected()); }

  bool isGround();
  bool isPropositional();
  bool isHorn();

  VirtualIterator<unsigned> getVariableIterator();

#if VDEBUG
  bool contains(Literal* lit);
  void assertValid();
#endif

  /** Mark clause as input clause for the saturation algorithm */
  void markInput() { _input=1; }
  /** Clause is an input clause for the saturation algorithm */
  bool isInput() { return _input; }


  SplitSet* splits() const { return _splits; }
  bool noSplits() const;
  void setSplits(SplitSet* splits) {
    CALL("Clause::setSplits");
    ASS(!_splits);
    _splits=splits;
  }

  VirtualIterator<string> toSimpleClauseStrings();


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
    if(_auxCurrTimestamp==0) {
      INVALID_OPERATION("Auxiliary clause value timestamp overflow!");
    }
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

  unsigned splitWeight() const;
  unsigned getNumeralWeight();
  float getEffectiveWeight(const Shell::Options& opt);

  void collectVars(DHSet<unsigned>& acc);
  unsigned varCnt();

  static ClauseEvent beforePropChange;
  static ClauseEvent afterPropChange;

protected:
  /** number of literals */
  unsigned _length : 29;
  /** clause color, or COLOR_INVALID if not determined yet */
  mutable unsigned _color : 2;
  /** clause is an input clause for the saturation algorithm */
  unsigned _input : 1;
  /** number of selected literals */
  unsigned _selected;
  /** age */
  unsigned _age;
  /** weight */
  mutable unsigned _weight;
  /** storage class */
  Store _store;
  /** in active index **/
  bool _in_active;
  /** number of references to this clause by inference rules */
  unsigned _inferenceRefCnt;
  /** timestamp marking when has the clause been reduced or restored by a backtracking splitting most recently */
  unsigned _reductionTimestamp;
  /** a map that translates Literal* to its index in the clause */
  InverseLookup<Literal>* _literalPositions;

  SplitSet* _splits;

  size_t _auxTimestamp;
  void* _auxData;

  static size_t _auxCurrTimestamp;
#if VDEBUG
  static bool _auxInUse;
#endif

  /** Array of literals of this unit */
  Literal* _literals[1];
}; // class Clause

}

#endif
