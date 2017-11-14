
/*
 * File Constraint.cpp.
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
 * @file Kernel/Constraint.cpp
 * Implements class Constraint.
 */
#if GNUMP
#include <sstream>

#include "Lib/Comparison.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Sort.hpp"
#include "Lib/Stack.hpp"

#include "Shell/UIHelper.hpp"

#include "Constraint.hpp"

using namespace Kernel;
using namespace std;
using namespace Shell;

unsigned Constraint::Coeff::hash(const Coeff& c)
{
  CALL("Constraint::Coeff::hash");

  return Hash::combineHashes(c.var, CoeffNumber::hash(c.value));
}

/**
 * Return coefficients of the constraint in ascending order.
 */
Constraint::CoeffIterator Constraint::coeffs() const
{
  CALL("Constraint::coeffs");

  return CoeffArray::Iterator(const_cast<CoeffArray&>(_coeffs));
}

/**
 * Return index of coefficient with variable @c v, or -1 if the variable
 * is not present
 */
int Constraint::getVarIdx(Var v) const
{
  CALL("Constraint::getVarIdx");

  switch(coeffCnt()) {
  case 0: return -1;
  case 1: return (*this)[0].var==v ? 0 : -1;
  case 2:
    if((*this)[0].var==v) {
      return 0;
    }
    else if((*this)[1].var==v) {
      return 1;
    }
    return -1;
  case 3:
    switch(Int::compare((*this)[1].var,v)) {
    case EQUAL: return 1;
    case GREATER: return (*this)[0].var==v ? 0 : -1;
    case LESS: return (*this)[2].var==v ? 2 : -1;
    }
    ASSERTION_VIOLATION;
    break;
  default: break;
  }

  size_t l=0;
  size_t r=coeffCnt();
  while(l<r) {
    size_t m = (l+r)/2; //may overflow
    switch(Int::compare((*this)[m].var,v)) {
    case EQUAL: return m;
    case GREATER:
      r=m;
      break;
    case LESS:
      l=m+1;
      break;
    }
  }
  return -1;
}

bool Constraint::hasVar(Var v) const
{
  CALL("Constraint::hasVar");

  int idx = getVarIdx(v);
  ASS(idx==-1 || (*this)[idx].var==v);
  return idx!=-1;
}

/**
 * Return reference to coefficient that contains variable @c v
 *
 * The constraint must contain variable @c v.
 */
const Constraint::Coeff& Constraint::getCoeff(Var v) const
{
  CALL("Constraint::getCoeff");

  int idx = getVarIdx(v);
  ASS(idx!=-1);
  ASS_EQ((*this)[idx].var,v);
  return (*this)[idx];
}

/**
 * Multiply all coefficients (including the free coefficient)
 * by the non-zero number @c num. If num is positive, the constraint
 * after the call is equivalent to the one before.
 */
void Constraint::multiplyCoeffs(CoeffNumber num)
{
  CALL("Constraint::multiplyCoeffs");
  ASS(!num.isZero());
  _freeCoeff *= num;
  size_t ccnt = coeffCnt();
  for(size_t i=0; i<ccnt; i++) {
	  _coeffs[i].value *= num;
  }
}

/**
 * Try to replace the constraint with an equivalent one that contains nicer numbers.
 */
void Constraint::reduce(bool allowDecimals)
{
  CALL("Constraint::reduce");

  static Stack<CoeffNumber*> nums;
  nums.reset();

  nums.push(&_freeCoeff);
  size_t ccnt = coeffCnt();
  for(size_t i=0; i<ccnt; i++) {
    nums.push(&_coeffs[i].value);
  }
  CoeffNumber::reduceNumbers(nums.size(), nums.begin(), allowDecimals);
}

vstring Constraint::toString() const
{
  CALL("Constraint::toString");

  vostringstream stm;
  UIHelper::outputConstraint(*this, stm);
  return stm.str();
}

bool Constraint::operator==(const Constraint& o) const
{
  CALL("Constraint::operator==");

  if(coeffCnt()!=o.coeffCnt() || freeCoeff()!=o.freeCoeff()) {
    return false;
  }
  CoeffIterator coeffs1;
  CoeffIterator coeffs2;
  while(coeffs1.hasNext()) {
    ALWAYS(coeffs2.hasNext());
    if(coeffs1.next()!=coeffs2.next()) {
      return false;
    }
  }
  ASS(!coeffs2.hasNext());
  return true;
}

Constraint* Constraint::clone(Constraint& c)
{
  return fromSortedIterator(c.type(), c.coeffs(), c.freeCoeff());
}

Constraint* Constraint::resolve(Var resolvedVar, Constraint& c1, Constraint& c2, bool allowDecimalCoeffitiets)
{
  CALL("Constraint::resolve");
  ASS_REP2(!c1.isEquality(), c1.type(), c1.toString());
  ASS(!c2.isEquality());

  typedef Stack<Coeff> CoeffStack;

  CoeffNumber rc1;
  CoeffNumber rc2;
#if VDEBUG
  rc1 = CoeffNumber::zero();
  rc2 = CoeffNumber::zero();
#endif
  static CoeffStack otherC1;
  static CoeffStack otherC2;
  otherC1.reset();
  otherC2.reset();

  CoeffIterator cit = c1.coeffs();
  while(cit.hasNext()) {
    const Coeff& c = cit.next();
    if(c.var==resolvedVar) {
      ASS_REP(rc1.isZero(), c1.toString()); //each variable can appear in a constraint only once
      rc1 = c.value;
    }
    else {
      otherC1.push(c);
    }
  }
  ASS_NEQ(rc1, CoeffNumber::zero()); //when we resolve on a variable, it must have non-zero coefficient
  cit = c2.coeffs();
  while(cit.hasNext()) {
    const Coeff& c = cit.next();
    if(c.var==resolvedVar) {
      ASS_REP(rc2.isZero(), c1.toString()); //each variable can appear in a constraint only once
      rc2 = c.value;
    }
    else {
      otherC2.push(c);
    }
  }
  ASS_NEQ(rc2, CoeffNumber::zero()); //when we resolve on a variable, it must have non-zero coefficient

  ASS_L(rc1*rc2, CoeffNumber::zero()); //the coefficient of resolved variable must be negative in exactly one constraint

  ConstraintType resType = (c1.type()==CT_GREQ && c2.type()==CT_GREQ) ? CT_GREQ : CT_GR;

  //coefficients in the otherC1 and otherC2 stacks are sorted because they're sorted in constraints as well

  CoeffNumber c1Mul = rc2.abs();
  CoeffNumber c2Mul = rc1.abs();

  static CoeffStack acc;
  acc.reset();

  CoeffNumber val;

  while(otherC1.isNonEmpty() || otherC2.isNonEmpty()) {
    while(otherC1.isNonEmpty() && (otherC2.isEmpty() || otherC1.top().var>otherC2.top().var) ) {
      Var var = otherC1.top().var;
      val = c1Mul*otherC1.pop().value;
      //cout<<"push var val "<<var<<val;
      ASS(!val.isZero());
      acc.push(Coeff(var, val));
    }
    while(otherC2.isNonEmpty() && (otherC1.isEmpty() || otherC2.top().var>otherC1.top().var) ) {
      Var var = otherC2.top().var;
      val = c2Mul*otherC2.pop().value;
      //cout<<"push var val "<<var<<val;
      ASS(!val.isZero());
      acc.push(Coeff(var, val));
    }
    while(otherC1.isNonEmpty() && otherC2.isNonEmpty() && otherC1.top().var==otherC2.top().var) {
      Var var = otherC1.top().var;
      val = (c1Mul*otherC1.pop().value) + (c2Mul*otherC2.pop().value);
      //cout<<"push var val last one"<<var<<val;
      //ASS(!val.isZero());
      if(!val.isZero()) {
    	  acc.push(Coeff(var, val));
      }
    }
  }

  val = c1Mul*c1.freeCoeff() + c2Mul*c2.freeCoeff();
  //cout<<"coeff value"<< val<<endl;
  Constraint* res = fromSortedIterator(resType, pvi( CoeffStack::TopFirstIterator(acc) ), val);
  //cout<<res->toString()<<endl;
  //cout<<c1.toString()<<" and "<<c2.toString()<<endl;
  res->reduce(allowDecimalCoeffitiets);
  return res;
}

#endif //GNUMP
