
/*
 * File Constraint.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Kernel/Constraint.hpp
 * Defines class Constraint.
 */

#ifndef __Constraint__
#define __Constraint__
#if GNUMP

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DArray.hpp"

#include "Number.hpp"

namespace Kernel {

enum ConstraintType {
  CT_GR,
  CT_GREQ,
  CT_EQ
};

/**
 * Constraint object
 *
 * Object represents a constraint
 *
 * c0*x0 + ... + cN*xN # C
 *
 * where c0,x0,...cN,xN come from the @c _coeffs array, C is equal to @c _constVat
 * and # is either >, >= or =, depending on @c _type.
 *
 * The coefficients are sorted in ascending order by variable number.
 */
class Constraint {
public:

  struct Coeff {
    Coeff() {}
    Coeff(Var var, const CoeffNumber& value) : var(var), value(value) {}

    bool isPositive() const { return value.isPositiveAssumingNonzero(); }
    bool isNegative() const { return value.isNegativeAssumingNonzero(); }

    bool operator==(const Coeff& o) const
    { return var==o.var && value==o.value; }
    bool operator!=(const Coeff& o) const
    { return !(*this==o); }

    static unsigned hash(const Coeff& c);

    Var var;
    CoeffNumber value;
  };
  typedef DArray<Coeff> CoeffArray;
  typedef DArray<Coeff>::Iterator CoeffIterator;

  const CoeffNumber& freeCoeff() const { return _freeCoeff; }
  ConstraintType type() const { return _type; }
  void setType(ConstraintType t) { _type = t; }

  /**
   * Return true if constraint was generated as a collapsing constraint.
   *
   * Input constraints can too appear as collapsing constraints, but
   * for those the mark is not set.
   */
  bool collapsing() const { return _collapsing; }
  void markCollapsing() { ASS(!_collapsing); _collapsing = true; }

  size_t coeffCnt() const { return _coeffs.size(); }
  CoeffIterator coeffs() const;
  const CoeffArray& coeffArray() const { return _coeffs; }
  const Coeff& operator[](unsigned i) const { return _coeffs[i]; }
  int getVarIdx(Var v) const;
  bool hasVar(Var v) const;
  const Coeff& getCoeff(Var v) const;

  void multiplyCoeffs(CoeffNumber num);
  void reduce(bool allowDecimals=true);

  bool isEquality() const { return type()==CT_EQ; }

  bool isTautology() const {
    ASS(!isEquality());
    return coeffCnt()==0
	&& (freeCoeff().isNegative() || (freeCoeff().isZero() && type()==CT_GREQ));
  }

  bool isRefutation() const {
    ASS(!isEquality());
    return coeffCnt()==0
	&& (freeCoeff().isPositive() || (freeCoeff().isZero() && type()==CT_GR));
  }

  vstring toString() const;

  void incRefCnt() { _refCnt++; }
  void decRefCnt() {
    _refCnt--;
    if(_refCnt==0) {
      delete this;
    }
  }

  bool operator==(const Constraint& o) const;
  bool operator!=(const Constraint& o) const
  { return !(*this==o); }
private:
  /**
   * Comparator that allows to order coeffitients by their variable
   * number (in ascending number)
   */
  struct CoeffComparator {
    Comparison compare(Coeff& c1, Coeff& c2) {
      return DefaultComparatorTKV::compare(c1.var, c2.var);
    }
  };
public:

  /**
   * Create a constraint of type @c t, with coefficients from @c coeffIterator and with
   * the constant value @c constVal. Each variable can appear only once among the
   * coefficients. Coefficients must be non-zero.
   */
  template<class Iter>
  static Constraint* fromIterator(ConstraintType t, Iter coeffIterator, const CoeffNumber& freeCoeff)
  {
    CALL("Constraint::fromIterator");

    Constraint* res = new Constraint();
    res->_coeffs.initFromIterator(coeffIterator);
    res->_freeCoeff = freeCoeff;
    res->_type = t;

    res->_coeffs.sort(CoeffComparator());

#if VDEBUG
    for(size_t i=0; i<res->_coeffs.size(); i++) {
      if(i>0) {
          ASS_G(res->_coeffs[i].var,res->_coeffs[i-1].var);
      }
      ASS_REP2(!res->_coeffs[i].value.isZero(), res->toString(), i);
    }
#endif

    return res;
  }

  /**
   * Create a constraint of type @c t, with coeffitients from @c coeffIterator and with
   * the constant value @c constVal. Variables are allowed to appear multiple times among
   * the coeffitients.
   */
  template<class Iter>
  static Constraint* fromBagIterator(ConstraintType t, Iter coeffIterator, const CoeffNumber& freeCoeff)
  {
    CALL("Constraint::fromBagIterator");

    static CoeffArray bag;
    bag.initFromIterator(coeffIterator);
    bag.sort(CoeffComparator());

    unsigned bagSize = bag.size();
    unsigned rIdx = 1;
    unsigned wIdx = 0;
    while(rIdx<bagSize) {
      ASS_L(wIdx, rIdx);
      if(bag[wIdx].var==bag[rIdx].var) {
	bag[wIdx].value+=bag[rIdx].value;
      }
      else {
	ASS_L(bag[wIdx].var,bag[rIdx].var);
	if(!bag[wIdx].value.isZero()) {
	  wIdx++;
	}
	if(wIdx!=rIdx) {
	  bag[wIdx]=bag[rIdx];
	}
      }
      rIdx++;
    }
    if(bag[wIdx].value.isZero()) {
      bag.shrink(wIdx);
    }
    else {
      bag.shrink(wIdx+1);
    }
    return fromSortedIterator(t, CoeffArray::Iterator(bag), freeCoeff);
  }

  /**
   * Create a constraint of type @c t, with coeffitients from @c coeffIterator and with
   * the constant value @c constVal. The coeffitients in @c coeffIterator must be in
   * ascending order. Each variable can appear only once among the coeffitients.
   * Coeffitients must be non-zero.
   */
  template<class Iter>
  static Constraint* fromSortedIterator(ConstraintType t, Iter coeffIterator, const CoeffNumber& freeCoeff)
  {
    CALL("Constraint::fromSortedIterator");

    Constraint* res = new Constraint();
    res->_coeffs.initFromIterator(coeffIterator);
    res->_freeCoeff = freeCoeff;
    res->_type = t;

#if VDEBUG
    for(size_t i=0; i<res->_coeffs.size(); i++) {
      if(i>0) {
	ASS_G(res->_coeffs[i].var, res->_coeffs[i-1].var);
      }
      ASS_REP2(!res->_coeffs[i].value.isZero(), res->toString(), i);
    }
#endif

    return res;
  }

  static Constraint* resolve(Var resolvedVar, Constraint& c1, Constraint& c2,
      bool allowDecimalCoeffitiets=true);
  static Constraint* clone(Constraint& c);

  CLASS_NAME("Constraint");
  USE_ALLOCATOR(Constraint);
private:
  Constraint() : _collapsing(false), _refCnt(0) {}

  /** Coeffitients with variables in ascending order */
  CoeffArray _coeffs;
  CoeffNumber _freeCoeff;
  ConstraintType _type;
  /**
   * @see collapsing()
   */
  bool _collapsing;
  unsigned _refCnt;
};

}
#endif //GNUMP
#endif // __Constraint__
