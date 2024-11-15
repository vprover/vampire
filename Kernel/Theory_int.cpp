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
 * @file Theory.cpp
 * Implements class Theory.
 */

#include <cmath>

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/BitUtils.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Shell/Skolem.hpp"

#include "Signature.hpp"
#include "SortHelper.hpp"
#include "OperatorType.hpp"
#include "Term.hpp"
#include "Kernel/NumTraits.hpp"

#include "Theory.hpp"
#define USES_2_COMPLEMENT (~0 == -1)

namespace Kernel
{

using namespace Lib;

///////////////////////
// IntegerConstantType
//

IntegerConstantType::IntegerConstantType(const vstring& str)
{

  if (!Int::stringToInt(str, _val)) {
    throw MachineArithmeticException();
  }
}

IntegerConstantType IntegerConstantType::operator+(const IntegerConstantType& num) const
{

  InnerType res;
  if (!Int::safePlus(_val, num._val, res)) {
    throw MachineArithmeticException();
  }
  return IntegerConstantType(res);
}

IntegerConstantType IntegerConstantType::operator-(const IntegerConstantType& num) const
{

  InnerType res;
  if (!Int::safeMinus(_val, num._val, res)) {
    throw MachineArithmeticException();
  }
  return IntegerConstantType(res);
}

IntegerConstantType IntegerConstantType::operator-() const
{

  InnerType res;
  if (!Int::safeUnaryMinus(_val, res)) {
    throw MachineArithmeticException();
  }
  return IntegerConstantType(res);
}

IntegerConstantType IntegerConstantType::operator*(const IntegerConstantType& num) const
{

  InnerType res;
  if (!Int::safeMultiply(_val, num._val, res)) {
    throw MachineArithmeticException();
  }
  return IntegerConstantType(res);
}

inline typename IntegerConstantType::InnerType divideOrThrow(typename IntegerConstantType::InnerType lhs, typename IntegerConstantType::InnerType rhs) {
    typename IntegerConstantType::InnerType out;
    if (!Int::safeDivide(lhs,rhs, out)) {
      throw MachineArithmeticException();
    }
    return out;
}

IntegerConstantType IntegerConstantType::intDivide(const IntegerConstantType& num) const 
{
    ASS_REP(num.divides(*this),  num.toString() + " does not divide " + this->toString() );
    return divideOrThrow(_val, num._val);
}

IntegerConstantType IntegerConstantType::remainderE(const IntegerConstantType& num) const
{

  if (num._val == 0) {
    throw DivByZeroException();
  }

  if (this->_val == numeric_limits<IntegerConstantType::InnerType>::min() && num._val == -1) {
    return 0;
  }

  auto mod = IntegerConstantType(this->_val % num._val);
  if (mod < 0) {
    if (num._val >= 0) {
      mod = mod + num;
    } else {
      mod = mod - num;
    }
  }
  return mod;
}

int IntegerConstantType::unwrapInt() const
{
  return _val;
}

IntegerConstantType IntegerConstantType::log2() const
{
  ASS_G(_val, 0)
  return IntegerConstantType(BitUtils::log2((unsigned)_val));
}

Kernel::RationalConstantType::RationalConstantType(int num, int den)
  : _num(num), _den(den)
{ cannonize(); }

Kernel::RationalConstantType::RationalConstantType(int num)
  : _num(num), _den(IntegerConstantType(1))
{}

Kernel::RationalConstantType::RationalConstantType(Kernel::IntegerConstantType num)
  : _num(num), _den(IntegerConstantType(1))
{}

RationalConstantType RationalConstantType::abs() const
{
  ASS_G(_den, 0)
  return RationalConstantType(_num.abs(), _den);
}
RationalConstantType RealConstantType::representation() const
{ return *this; }

RealConstantType RealConstantType::abs() const
{
  return RealConstantType(RationalConstantType(*this).abs());
}

IntegerConstantType IntegerConstantType::inverseModulo(IntegerConstantType const& m) const 
{ 
#warn "using naive version of inverse modulo m. This is very slow. implement the extended version of the euclidean algorithm, or use the gmp version of theory reasoning if you want high performing vampire."
  return naiveInverseModulo(*this, m); 
}

IntegerConstantType IntegerConstantType::abs() const
{
  if (toInner() == std::numeric_limits<InnerType>::min() && USES_2_COMPLEMENT) {
    throw MachineArithmeticException();
  }
  return IntegerConstantType(::std::abs(toInner()));
}

/**
 * specification from TPTP:
 * quotient_e(N,D) - the Euclidean quotient, which has a non-negative remainder. If D is positive then $quotient_e(N,D) is the floor (in the type of N and D) of the real division N/D, and if D is negative then $quotient_e(N,D) is the ceiling of N/D.
 */
IntegerConstantType IntegerConstantType::quotientE(const IntegerConstantType& num) const
{ 

  if (num._val == 0) {
    throw DivByZeroException();
  }

  if (this->_val == numeric_limits<IntegerConstantType::InnerType>::min() && num._val == -1) {
    throw MachineArithmeticException();
  }

  // as in remainderE
  auto mod = IntegerConstantType(this->_val % num._val);

  // return (*this - this->remainderE(num)).intDivide(num); // the clean definition; but we don't want to subtract for small *this

  if (mod < 0) {
    // as in remainderE -- effectively adjust for the computation of the positive mod
    if (num._val >= 0) {
      return (*this - mod).intDivide(num)-1;
    } else {
      return (*this - mod).intDivide(num)+1;
    }
  } else {
    if (*this < 0) { // we don't want to subtract a positive mod, counterbalance with num, adjusting with +/-1
      if (num._val >= 0) {
        return (*this + num - mod).intDivide(num)-1;
      } else {
        return (*this - num - mod).intDivide(num)+1;
      }
    } else {
      return (*this - mod).intDivide(num);
    }
  }
}

IntegerConstantType IntegerConstantType::quotientF(const IntegerConstantType& num) const
{ 
  if(num.divides(*this)){
    return IntegerConstantType(intDivide(num));
  }
  return IntegerConstantType(::floor(realDivide(num)));
}

IntegerConstantType IntegerConstantType::quotientT(const IntegerConstantType& num) const
{ 
  if(num.divides(*this)){
    return IntegerConstantType(intDivide(num));
  }
  return IntegerConstantType(::trunc(realDivide(num)));
}

IntegerConstantType IntegerConstantType::remainderF(const IntegerConstantType& num) const
{ return (*this) - num * quotientF(num); } 

IntegerConstantType IntegerConstantType::remainderT(const IntegerConstantType& num) const
{ return (*this) - num * quotientT(num); }


bool IntegerConstantType::divides(const IntegerConstantType& num) const 
{
  if (_val == 0) { return false; }
  if (num._val == _val) { return true; }
  if (num._val == numeric_limits<decltype(num._val)>::min() && _val == -1) {
    return true;
  } else {
    return ( num._val % _val == 0);
  }
}

//TODO remove this operator. We already have 3 other ways of computing the remainder, required by the semantics of TPTP and SMTCOMP.
IntegerConstantType IntegerConstantType::operator%(const IntegerConstantType& num) const
{

  //TODO: check if modulo corresponds to the TPTP semantic
  if (num._val==0) {
    throw DivByZeroException();
  }
  return IntegerConstantType(_val%num._val);
}

bool IntegerConstantType::operator==(const IntegerConstantType& num) const
{

  return _val==num._val;
}

bool IntegerConstantType::operator>(const IntegerConstantType& num) const
{

  return _val>num._val;
}

IntegerConstantType IntegerConstantType::floor(IntegerConstantType x)
{ return x; }

IntegerConstantType IntegerConstantType::floor(RationalConstantType rat)
{

  IntegerConstantType num = rat.numerator();
  IntegerConstantType den = rat.denominator();
  if (den == IntegerConstantType(1)) {
    return num;
  }
  /* there is a non-zero remainder for num / den */
  ASS_G(den, 0);
  if (num >= IntegerConstantType(0)) {
    return IntegerConstantType(num.toInner() /den.toInner());
  } else  {
    return IntegerConstantType(num.toInner() / den.toInner() - 1);
  }
}

IntegerConstantType IntegerConstantType::ceiling(IntegerConstantType x)
{ return x; }

Sign IntegerConstantType::sign() const 
{ return _val > 0 ? Sign::Pos 
       : _val < 0 ? Sign::Neg 
       :            Sign::Zero; }

Sign RealConstantType::sign() const 
{ return RationalConstantType::sign(); }

Sign RationalConstantType::sign() const 
{ 
  ASS_EQ(denominator().sign(), Sign::Pos)
  return numerator().sign(); 
}

/** 
 * TPTP spec:
 * The smallest integral number not less than the argument. 
 */
IntegerConstantType IntegerConstantType::ceiling(RationalConstantType rat)
{

  IntegerConstantType num = rat.numerator();
  IntegerConstantType den = rat.denominator();
  if (den == IntegerConstantType(1)) {
    return num;
  }
  /* there is a remainder for num / den */
  ASS_G(den, 0);
  if (num >= IntegerConstantType(0)) {
    return IntegerConstantType(num.toInner() /den.toInner() + 1);
  } else  {
    return IntegerConstantType(num.toInner() / den.toInner());
  }
}

Comparison IntegerConstantType::comparePrecedence(IntegerConstantType n1, IntegerConstantType n2)
{
  try {
    if (n1 == numeric_limits<InnerType>::min()) {
      if (n2 == numeric_limits<InnerType>::min()) {
        return EQUAL;
      } else {
        return GREATER;
      }
    } else {
      if (n2 == numeric_limits<InnerType>::min()) {
        return LESS;
      } else {
        InnerType an1 = n1.abs().toInner();
        InnerType an2 = n2.abs().toInner();

        ASS_GE(an1,0);
        ASS_GE(an2,0);

        return an1 < an2 ? LESS : (an1 == an2 ? // compare the signed ones, making negative greater than positive
            static_cast<Comparison>(-Int::compare(n1.toInner(), n2.toInner()))
                              : GREATER);
      }
    }
  }
  catch(ArithmeticException& e) {
    ASSERTION_VIOLATION;
    throw e;
  }
}

vstring IntegerConstantType::toString() const
{

  return Int::toString(_val);
}

///////////////////////
// RationalConstantType
//

RationalConstantType::RationalConstantType(InnerType num, InnerType den)
{

  init(num, den);
}

RationalConstantType::RationalConstantType(const vstring& num, const vstring& den)
{

  init(InnerType(num), InnerType(den));
}

void RationalConstantType::init(InnerType num, InnerType den)
{

  _num = num;
  _den = den;
  cannonize();

  // Dividing by zero is bad!
  if(_den.toInner()==0) throw DivByZeroException();
}

RationalConstantType RationalConstantType::operator+(const RationalConstantType& o) const
{

  if (_den==o._den) {
    return RationalConstantType(_num + o._num, _den);
  }
  return RationalConstantType(_num*o._den + o._num*_den, _den*o._den);
}

RationalConstantType RationalConstantType::operator-(const RationalConstantType& o) const
{

  return (*this) + (-o);
}

RationalConstantType RationalConstantType::operator-() const
{

  return RationalConstantType(-_num, _den);
}

RationalConstantType RationalConstantType::operator*(const RationalConstantType& o) const
{

  return RationalConstantType(_num*o._num, _den*o._den);
}

RationalConstantType RationalConstantType::operator/(const RationalConstantType& o) const
{
  auto lhs = *this;
  auto rhs = o;
  return RationalConstantType(
      lhs._num * rhs._den, 
      lhs._den * rhs._num);
}

bool RationalConstantType::isInt() const
{

  return _den==1;
}

bool RationalConstantType::operator==(const RationalConstantType& o) const
{

  return _num==o._num && _den==o._den;
}

bool RationalConstantType::operator>(const RationalConstantType& o) const
{
  /* prevents overflows */
  auto toLong = [](IntegerConstantType t)  -> long int
  { return  t.toInner(); };

  return toLong(_num)*toLong(o._den)>(toLong(o._num)*toLong(_den));
}


vstring RationalConstantType::toString() const
{

  vstring numStr = _num.toString();
  vstring denStr = _den.toString();

//  return "("+numStr+"/"+denStr+")";
  return numStr+"/"+denStr;
}

IntegerConstantType IntegerConstantType::lcm(IntegerConstantType const& l, IntegerConstantType const& r)
{ 
  ASS(l > IntegerConstantType(0))
  ASS(r > IntegerConstantType(0))
  // both are positive, hence it doesn't matter which quotient we use.
  return l * (r.quotientE(gcd(l,r))); 
}

IntegerConstantType IntegerConstantType::gcd(IntegerConstantType const& l, IntegerConstantType const& r)
{ return IntegerConstantType(Int::gcd(l.toInner(), r.toInner())); }

/**
 * Ensure the GCD of numerator and denominator is 1, and the only
 * number that may be negative is numerator
 */
void RationalConstantType::cannonize()
{

  unsigned gcd = Int::gcd(_num.toInner(), _den.toInner());
  if (gcd == (unsigned)(-(long long)(numeric_limits<int>::min()))) { // we are talking about 2147483648, but I can't take minus of it's int representation!
    ASS_EQ(_num, numeric_limits<int>::min());
    ASS_EQ(_den, numeric_limits<int>::min());
    _num = 1;
    _den = 1;
    return;
  }

  // now it's safe to treat this unsigned as signed
  ASS_LE(gcd,(unsigned)numeric_limits<signed>::max());
  if (gcd!=1) {
    _num = _num.intDivide(gcd);
    _den = _den.intDivide(gcd);
  }
  if (_den<0) {
    _num = -_num;
    _den = -_den;
  }
  // Normalize zeros
  // If it is of the form 0/c then rewrite it to 0/1
  // Unless it is of the form 0/0
  if(_num==0 && _den!=0){ _den=1; }
}
 
Comparison RationalConstantType::comparePrecedence(RationalConstantType n1, RationalConstantType n2)
{
  /* cannot overflow */
  auto prec = IntegerConstantType::comparePrecedence(n1._den, n2._den);
  if (prec != EQUAL) return prec;
  return IntegerConstantType::comparePrecedence(n1._num, n2._num);
  
  // try {
  //
  //   if (n1==n2) { return EQUAL; }
  //
  //   bool haveRepr1 = true;
  //   bool haveRepr2 = true;
  //
  //   IntegerConstantType repr1, repr2;
  //
  //   try {
  //     repr1 = n1.numerator()+n1.denominator();
  //   } catch(ArithmeticException&) {
  //     haveRepr1 = false;
  //   }
  //
  //   try {
  //     repr2 = n2.numerator()+n2.denominator();
  //   } catch(ArithmeticException&) {
  //     haveRepr2 = false;
  //   }
  //
  //   if (haveRepr1 && haveRepr2) {
  //     Comparison res = IntegerConstantType::comparePrecedence(repr1, repr2);
  //     if (res==EQUAL) {
	// res = IntegerConstantType::comparePrecedence(n1.numerator(), n2.numerator());
  //     }
  //     ASS_NEQ(res, EQUAL);
  //     return res;
  //   }
  //   if (haveRepr1 && !haveRepr2) {
  //     return LESS;
  //   }
  //   if (!haveRepr1 && haveRepr2) {
  //     return GREATER;
  //   }
  //
  //   ASS(!haveRepr1);
  //   ASS(!haveRepr2);
  //
  //   Comparison res = IntegerConstantType::comparePrecedence(n1.denominator(), n2.denominator());
  //   if (res==EQUAL) {
  //     res = IntegerConstantType::comparePrecedence(n1.numerator(), n2.numerator());
  //   }
  //   ASS_NEQ(res, EQUAL);
  //   return res;
  // }
  // catch(ArithmeticException&) {
  //   ASSERTION_VIOLATION;
  //   throw;
  // }
}


///////////////////////
// RealConstantType
//

Comparison RealConstantType::comparePrecedence(RealConstantType n1, RealConstantType n2)
{

  return RationalConstantType::comparePrecedence(n1, n2);
}

bool RealConstantType::parseDouble(const vstring& num, RationalConstantType& res)
{

  try {
    vstring newNum;
    IntegerConstantType denominator = 1;
    bool haveDecimal = false;
    bool neg = false;
    size_t nlen = num.size();
    for(size_t i=0; i<nlen; i++) {
      if (num[i]=='.') {
	if (haveDecimal) {
	  return false;
	}
	haveDecimal = true;
      }
      else if (i==0 && num[i]=='-') {
	neg = true;
      }
      else if (num[i]>='0' && num[i]<='9') {
	if (newNum=="0") {
	  newNum = num[i];
	}
	else {
	  newNum += num[i];
	}
	if (haveDecimal) {
	  denominator = denominator * 10;
	}
      }
      else {
	return false;
      }
    }
    if (neg) {
      newNum = '-'+newNum;
    }
    IntegerConstantType numerator(newNum);
    res = RationalConstantType(numerator, denominator);
  } catch(ArithmeticException&) {
    return false;
  }
  return true;
}


RealConstantType::RealConstantType(const vstring& number)
{

  RationalConstantType value;
  if (parseDouble(number, value)) {
    init(value.numerator(), value.denominator());
    return;
  }

  double numDbl;
  if (!Int::stringToDouble(number, numDbl)) {
    throw MachineArithmeticException();
  }
  InnerType denominator = 1;
  while(::floor(numDbl)!=numDbl) {
    denominator = denominator*10;
    numDbl *= 10;
  }

  if (numDbl > numeric_limits<InnerType::InnerType>::max() ||
      numDbl < numeric_limits<InnerType::InnerType>::min()) {
    //the numerator part of double doesn't fit inside the inner integer type
    throw MachineArithmeticException();
  }

  InnerType::InnerType numerator = static_cast<InnerType::InnerType>(numDbl);
  // the test below should now never trigger (thanks to the one above), but we include it to preserve the original semantics
  if (numerator!=numDbl) {
    //the numerator part of double doesn't fit inside the inner integer type
    throw MachineArithmeticException();
  }
  init(numerator, denominator);
}

vstring RealConstantType::toNiceString() const
{

  if (denominator().toInner()==1) {
    return numerator().toString()+".0";
  }
  float frep = (float) numerator().toInner() /(float) denominator().toInner();
  return Int::toString(frep);
  //return toString();
}

size_t IntegerConstantType::hash() const {
  return std::hash<decltype(_val)>{}(_val);
}

size_t RationalConstantType::hash() const {
  return (denominator().hash() << 1) ^ numerator().hash();
}

size_t RealConstantType::hash() const {
  return (denominator().hash() << 1) ^ numerator().hash();
}

std::ostream& operator<<(std::ostream& out, Sign const& self)
{ 
  switch(self) {
    case Sign::Zero: return out << "0";
    case Sign::Pos: return out << "+";
    case Sign::Neg: return out << "-";
  }
  ASSERTION_VIOLATION
}


}

