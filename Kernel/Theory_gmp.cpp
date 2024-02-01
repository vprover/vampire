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

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Shell/Skolem.hpp"

#include "Signature.hpp"
#include "SortHelper.hpp"
#include "OperatorType.hpp"
#include "Term.hpp"
#include "Kernel/NumTraits.hpp"
#include "Lib/StringUtils.hpp"

#include "Theory.hpp"

std::ostream& operator<<(std::ostream& out, mpz_class const& self)
{ 
  BYPASSING_ALLOCATOR;
  return out << self.get_str(); 
}

namespace Kernel
{

using namespace Lib;

///////////////////////
// IntegerConstantType
//

IntegerConstantType::IntegerConstantType(vstring const& str)
  : _val()
{
  CALL("IntegerConstantType::IntegerConstantType(vstring const&)");

  if (-1 == mpz_set_str(_val.get_mpz_t(), str.c_str(), /* base */ 10)) {
    throw UserErrorException("not a valit string literal: ", str);
  }
}

#define IMPL_BIN_OP(op) \
  IntegerConstantType IntegerConstantType::operator op (const IntegerConstantType& num) const \
  { return IntegerConstantType(this->_val op num._val); }

IMPL_BIN_OP(+)
IMPL_BIN_OP(-)
IMPL_BIN_OP(*)

// TODO operator(s) for move references ?!
IntegerConstantType IntegerConstantType::operator-() const
{ return IntegerConstantType(-_val); }

IntegerConstantType IntegerConstantType::intDivide(const IntegerConstantType& num) const 
{
  CALL("IntegerConstantType::intDivide");
  ASS_REP(num.divides(*this),  num.toString() + " does not divide " + this->toString() );
  ASS_REP(num._val != 0, "divisor must not be zero")

  mpz_class out;
  mpz_divexact(out.get_mpz_t(), _val.get_mpz_t(), num._val.get_mpz_t());
  return IntegerConstantType(out);
}

IntegerConstantType Kernel::IntegerConstantType::log2() const 
{
  ASS(_val >= 0);
  // TODO double check this
  size_t size = mpz_sizeinbase(_val.get_mpz_t(), 2);
  return IntegerConstantType(size - 1);
}


int Kernel::IntegerConstantType::unwrapInt() const 
{
  if (!_val.fits_sint_p()) {
    throw MachineArithmeticException("trying to unwrap too big integer");
  } else {
    return (int) mpz_get_si(_val.get_mpz_t());
  }
}

/**
 * specification from TPTP:
 * quotient_e(N,D) - the Euclidean quotient, which has a non-negative remainder. If D is positive then $quotient_e(N,D) is the floor (in the type of N and D) of the real division N/D, and if D is negative then $quotient_e(N,D) is the ceiling of N/D.
 */
IntegerConstantType IntegerConstantType::quotientE(const IntegerConstantType& num) const
{
  CALL("IntegerConstantType::remainderE");
  auto& n = this->_val;
  auto& d = num._val;
  mpz_class out;
  if (d > 0) {
    mpz_fdiv_q(out.get_mpz_t(), n.get_mpz_t(), d.get_mpz_t());
    //       ^ <- where it differes from remainderE
  } else if (d < 0) {
    mpz_cdiv_q(out.get_mpz_t(), n.get_mpz_t(), d.get_mpz_t());
    //       ^ <- where it differes from remainderE
  } else {
    ASS(d == 0)
    throw DivByZeroException();
  }
  return IntegerConstantType(std::move(out));
}
IntegerConstantType IntegerConstantType::remainderE(const IntegerConstantType& num) const
{
  CALL("IntegerConstantType::remainderE");
  auto& n = this->_val;
  auto& d = num._val;
  mpz_class out;
  if (d > 0) {
    mpz_fdiv_r(out.get_mpz_t(), n.get_mpz_t(), d.get_mpz_t());
    //       ^ <- where it differes from quotientE
  } else if (d < 0) {
    mpz_cdiv_r(out.get_mpz_t(), n.get_mpz_t(), d.get_mpz_t());
    //       ^ <- where it differes from quotientE
  } else {
    ASS(d == 0)
    throw DivByZeroException();
  }
  return IntegerConstantType(std::move(out));
}

Kernel::RationalConstantType::RationalConstantType(Kernel::IntegerConstantType n)
  : _num(std::move(n)), _den(1)
{ }

Kernel::RationalConstantType::RationalConstantType(int n)
  : _num(std::move(n)), _den(1)
{ }

Kernel::RationalConstantType::RationalConstantType(int n, int d)
  : RationalConstantType(IntegerConstantType(n), IntegerConstantType(d))
{ }

RationalConstantType RationalConstantType::abs() const
{
  ASS_G(_den, IntegerConstantType(0))
  return RationalConstantType(_num.abs(), _den);
}

// TODO get rid of this?
RationalConstantType RealConstantType::representation() const
{ return *this; }

RealConstantType RealConstantType::abs() const
{
  return RealConstantType(RationalConstantType(*this).abs());
}

IntegerConstantType IntegerConstantType::abs() const
{ return IntegerConstantType(::abs(toInner())); }

IntegerConstantType IntegerConstantType::quotientF(const IntegerConstantType& num) const
{ 
  ASS(num._val != 0)
  mpz_class out;
  mpz_fdiv_q(out.get_mpz_t(), this->_val.get_mpz_t(), num._val.get_mpz_t());
  //  ^    ^
  return IntegerConstantType(std::move(out));
}

IntegerConstantType IntegerConstantType::remainderF(const IntegerConstantType& num) const
{ 
  ASS(num._val != 0)
  mpz_class out;
  mpz_fdiv_r(out.get_mpz_t(), this->_val.get_mpz_t(), num._val.get_mpz_t());
  //  ^    ^
  return IntegerConstantType(std::move(out));
}

IntegerConstantType IntegerConstantType::quotientT(const IntegerConstantType& num) const
{ 
  ASS(num._val != 0)
  mpz_class out;
  mpz_tdiv_q(out.get_mpz_t(), this->_val.get_mpz_t(), num._val.get_mpz_t());
  //  ^    ^
  return IntegerConstantType(std::move(out));
}

IntegerConstantType IntegerConstantType::remainderT(const IntegerConstantType& num) const
{ 
  ASS(num._val != 0)
  mpz_class out;
  mpz_tdiv_r(out.get_mpz_t(), this->_val.get_mpz_t(), num._val.get_mpz_t());
  //  ^    ^
  return IntegerConstantType(std::move(out));
}

bool IntegerConstantType::divides(const IntegerConstantType& num) const 
{
  CALL("IntegerConstantType:divides");
  if (_val == 0) { return false; }
  if (num._val == _val) { return true; }
  mpz_class out;
  return 0 != mpz_divisible_p(num._val.get_mpz_t(), this->_val.get_mpz_t());
}

// //TODO remove this operator. We already have 3 other ways of computing the remainder, required by the semantics of TPTP and SMTCOMP.
// IntegerConstantType IntegerConstantType::operator%(const IntegerConstantType& num) const
// {
//   CALL("IntegerConstantType::operator%");
//
//   //TODO: check if modulo corresponds to the TPTP semantic
//   if (num._val==0) {
//     throw DivByZeroException();
//   }
//   return IntegerConstantType(_val%num._val);
// }

bool IntegerConstantType::operator==(const IntegerConstantType& num) const
{ return _val==num._val; }

bool IntegerConstantType::operator>(const IntegerConstantType& num) const
{ return _val>num._val; }

IntegerConstantType IntegerConstantType::floor(IntegerConstantType x)
{ return x; }

IntegerConstantType IntegerConstantType::floor(RationalConstantType rat)
{
  mpz_class out;
  mpz_fdiv_q(out.get_mpz_t(), 
             rat.numerator().toInner().get_mpz_t(), 
             rat.denominator().toInner().get_mpz_t());
  return IntegerConstantType(std::move(out));
}


IntegerConstantType IntegerConstantType::ceiling(RationalConstantType rat)
{
  mpz_class out;
  mpz_cdiv_q(out.get_mpz_t(), 
             rat.numerator().toInner().get_mpz_t(), 
             rat.denominator().toInner().get_mpz_t());
  return IntegerConstantType(std::move(out));
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

// /** 
//  * TPTP spec:
//  * The smallest integral number not less than the argument. 
//  */
// IntegerConstantType IntegerConstantType::ceiling(RationalConstantType rat)
// {
//   CALL("IntegerConstantType::ceiling");
//
//   IntegerConstantType num = rat.numerator();
//   IntegerConstantType den = rat.denominator();
//   if (den == IntegerConstantType(1)) {
//     return num;
//   }
//   /* there is a remainder for num / den */
//   ASS_G(den, 0);
//   if (num >= IntegerConstantType(0)) {
//     return IntegerConstantType(num.toInner() /den.toInner() + 1);
//   } else  {
//     return IntegerConstantType(num.toInner() / den.toInner());
//   }
// }

Comparison IntegerConstantType::comparePrecedence(IntegerConstantType n1, IntegerConstantType n2)
{
  CALL("IntegerConstantType::comparePrecedence");
  auto cmp = ::cmp(n1.abs().toInner(), n2.abs().toInner());
  if (cmp > 0) return Comparison::GREATER;
  if (cmp < 0) return Comparison::LESS;
  cmp = -::cmp(n1.toInner(), n2.toInner());
  if (cmp > 0) return Comparison::GREATER;
  if (cmp < 0) return Comparison::LESS;
  else return Comparison::EQUAL;
}

vstring IntegerConstantType::toString() const
{
  CALL("IntegerConstantType::toString");
  BYPASSING_ALLOCATOR;
  string s = _val.get_str();
  return vstring(s.c_str());
}
///////////////////////
// RationalConstantType
//

RationalConstantType::RationalConstantType(InnerType num, InnerType den)
  : _num(num), _den(den)
{ cannonize(); }

RationalConstantType::RationalConstantType(const vstring& num, const vstring& den)
  : RationalConstantType(InnerType(num), InnerType(den))
{ }

RationalConstantType RationalConstantType::operator+(const RationalConstantType& o) const
{
  CALL("RationalConstantType::operator+");

  if (_den==o._den) {
    return RationalConstantType(_num + o._num, _den);
  }
  return RationalConstantType(_num*o._den + o._num*_den, _den*o._den);
}

RationalConstantType RationalConstantType::operator-(const RationalConstantType& o) const
{
  CALL("RationalConstantType::operator-/1");

  return (*this) + (-o);
}

RationalConstantType RationalConstantType::operator-() const
{
  CALL("RationalConstantType::operator-/0");

  return RationalConstantType(-_num, _den);
}

RationalConstantType RationalConstantType::operator*(const RationalConstantType& o) const
{
  CALL("RationalConstantType::operator*");

  return RationalConstantType(_num*o._num, _den*o._den);
}

RationalConstantType RationalConstantType::operator/(const RationalConstantType& o) const
{
  auto &lhs = *this;
  auto &rhs = o;
  ASS(!rhs._num.isZero())
  return RationalConstantType(
      lhs._num * rhs._den, 
      lhs._den * rhs._num);
}

bool RationalConstantType::isInt() const
{
  return _den == IntegerConstantType(1);
}

bool RationalConstantType::operator==(const RationalConstantType& o) const
{
  CALL("IntegerConstantType::operator==");
  return _num==o._num && _den==o._den;
}

bool RationalConstantType::operator>(const RationalConstantType& o) const
{
  mpq_class l(  _num.toInner(),   _den.toInner());
  mpq_class r(o._num.toInner(), o._den.toInner());
  l.canonicalize();
  r.canonicalize();
  return l > r;
}

std::ostream& operator<<(std::ostream& out, IntegerConstantType const& self)
{ return out << self.toString(); }

std::ostream& operator<<(std::ostream& out, RationalConstantType const& self)
{ return out << self.numerator() << "/" << self.denominator(); }

std::ostream& operator<<(std::ostream& out, RealConstantType const& self)
{ return out << (RationalConstantType const&)self; }


vstring RationalConstantType::toString() const
{ return Lib::toString(*this); }

IntegerConstantType IntegerConstantType::lcm(IntegerConstantType const& l, IntegerConstantType const& r)
{ 
  ASS(l > IntegerConstantType(0))
  ASS(r > IntegerConstantType(0))
  // both are positive, hence it doesn't matter which quotient we use.
  return l * (r.quotientE(gcd(l,r))); 
}

IntegerConstantType IntegerConstantType::gcd(IntegerConstantType const& l, IntegerConstantType const& r)
{ 
  mpz_class out;
  mpz_gcd(out.get_mpz_t(), l._val.get_mpz_t(), r._val.get_mpz_t());
  return IntegerConstantType(std::move(out)); 
}

/**
 * Ensure the GCD of numerator and denominator is 1, and the only
 * number that may be negative is numerator
 */
void RationalConstantType::cannonize()
{
  CALL("RationalConstantType::cannonize");
  mpq_class q(_num.toInner(), _den.toInner());
  q.canonicalize();
  _num = IntegerConstantType(std::move(q.get_num()));
  _den = IntegerConstantType(std::move(q.get_den()));
}
 
Comparison RationalConstantType::comparePrecedence(RationalConstantType n1, RationalConstantType n2)
{
  auto prec = IntegerConstantType::comparePrecedence(n1._den, n2._den);
  if (prec != EQUAL) return prec;
  return IntegerConstantType::comparePrecedence(n1._num, n2._num);
}


///////////////////////
// RealConstantType
//

Comparison RealConstantType::comparePrecedence(RealConstantType n1, RealConstantType n2)
{ return RationalConstantType::comparePrecedence(n1, n2); }

bool RealConstantType::parseDouble(const vstring& num, RationalConstantType& res)
{
  CALL("RealConstantType::parseDouble");

  vstring newNum;
  IntegerConstantType denominator = IntegerConstantType(1);
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
        denominator = denominator * IntegerConstantType(10);
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
  return true;
}


RealConstantType::RealConstantType(const vstring& number)
  : RealConstantType()
{
  CALL("RealConstantType::RealConstantType");

  RationalConstantType value;
  if (parseDouble(number, value))  {
    *this = RealConstantType(std::move(value));
    return;
  } else {
    throw UserErrorException("invalid decimal literal");
  }
}

vstring RealConstantType::toNiceString() const
{
  return toString();
}

size_t IntegerConstantType::hash() const {
  return std::hash<decltype(_val.get_si())>{}(_val.get_si());
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

