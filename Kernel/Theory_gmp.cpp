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
#include <cstdio>
#include <iostream>

#include "mini-gmp.c"
#include "mini-mpq.c"

#include "Theory.hpp"

std::string to_string(mpz_t const& self) {
  auto s = mpz_sizeinbase(self, /* base */ 10);
  auto str = new char[s + 2];
  auto str_ = mpz_get_str(str, /* base */ 10, self);
  ASS_EQ(str_, str)
  return std::string(str);
}

std::ostream& operator<<(std::ostream& out, mpz_t const& self)
{ return out << to_string(self); }

namespace Kernel
{

using namespace Lib;

///////////////////////
// IntegerConstantType
//

IntegerConstantType::IntegerConstantType(std::string const& str)
  : _val()
{
  if (-1 == mpz_set_str(_val, str.c_str(), /* base */ 10)) {
    throw UserErrorException("not a valit string literal: ", str);
  }
}

#define IMPL_BIN_OP(fun, mpz_fun)                                                              \
  IntegerConstantType IntegerConstantType::fun(const IntegerConstantType& num) const \
  { auto out = IntegerConstantType(0); mpz_fun(out._val, this->_val, num._val); return out; } \

  // TODO move semantics
IMPL_BIN_OP(operator+, mpz_add)
IMPL_BIN_OP(operator-, mpz_sub)
IMPL_BIN_OP(operator*, mpz_mul)
IMPL_BIN_OP(lcm, mpz_lcm)
IMPL_BIN_OP(gcd, mpz_gcd)
IMPL_BIN_OP(inverseModulo, mpz_invert)

// TODO operator(s) for move references ?!
#define IMPL_UN_OP(fun, mpz_fun)                                                          \
  IntegerConstantType IntegerConstantType::fun() const                                    \
  {                                                                                       \
    auto out = IntegerConstantType(0);                                                    \
    mpz_fun(out._val, _val);                                                              \
    return out;                                                                           \
  }                                                                                       \

IMPL_UN_OP(operator-, mpz_neg)
IMPL_UN_OP(abs      , mpz_abs)

// TODO (?)
// IntegerConstantType IntegerConstantType::operator-() &&
// { 
//   mpz_neg(_val, _val);
//   return std::move(*this); 
// }

IntegerConstantType IntegerConstantType::intDivide(const IntegerConstantType& num) const 
{
  ASS_REP(num.divides(*this),  num.toString() + " does not divide " + this->toString() );
  ASS_REP(*this != 0, "divisor must not be zero")

  IntegerConstantType out;
  mpz_divexact(out._val, _val, num._val);
  return out;
}

IntegerConstantType Kernel::IntegerConstantType::log2() const 
{
  ASS(*this >= 0);
  size_t size = mpz_sizeinbase(_val, 2);
  return IntegerConstantType(size - 1);
}


int Kernel::IntegerConstantType::unwrapInt() const 
{
  if (!mpz_fits_sint_p(_val)) {
    throw MachineArithmeticException("trying to unwrap too big integer");
  } else {
    return (int) mpz_get_si(_val);
  }
}

/**
 * specification from TPTP:
 * quotient_e(N,D) - the Euclidean quotient, which has a non-negative remainder. If D is positive then $quotient_e(N,D) is the floor (in the type of N and D) of the real division N/D, and if D is negative then $quotient_e(N,D) is the ceiling of N/D.
 */
IntegerConstantType::QR IntegerConstantType::divE(const IntegerConstantType& num) const
{
  auto& n = *this;
  auto& d = num;
  auto out = QR { .quot = IntegerConstantType(0), .rem  = IntegerConstantType(0), };
  switch (d.sign()) {
    case Sign::Zero: 
      ASSERTION_VIOLATION;
      throw DivByZeroException();
    case Sign::Pos:
      mpz_fdiv_qr(out.quot._val, out.rem._val, n._val, d._val);
    case Sign::Neg:
      mpz_cdiv_qr(out.quot._val, out.rem._val, n._val, d._val);
  }
  return out;
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

IntegerConstantType::QR IntegerConstantType::divT(const IntegerConstantType& num) const
{ 
  ASS(num != 0)
  auto& n = *this;
  auto& d = num;
  auto out = QR { .quot = IntegerConstantType(0), .rem  = IntegerConstantType(0), };
  mpz_tdiv_qr(out.quot._val, out.rem._val, n._val, d._val);
  return out;
}

IntegerConstantType::QR IntegerConstantType::divF(const IntegerConstantType& num) const
{ 
  ASS(num != 0)
  auto& n = *this;
  auto& d = num;
  auto out = QR { .quot = IntegerConstantType(0), .rem  = IntegerConstantType(0), };
  mpz_fdiv_qr(out.quot._val, out.rem._val, n._val, d._val);
  return out;
}

bool IntegerConstantType::divides(const IntegerConstantType& num) const 
{
  if (*this == 0) { return false; }
  // if (num._val == _val) { return true; }
  return 0 != mpz_divisible_p(num._val, this->_val);
}

// //TODO remove this operator. We already have 3 other ways of computing the remainder, required by the semantics of TPTP and SMTCOMP.
// IntegerConstantType IntegerConstantType::operator%(const IntegerConstantType& num) const
// {
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

#define MK_ROUNDING(round, mpz_fun)                                                       \
  IntegerConstantType RationalConstantType::round() const                                 \
  {                                                                                       \
    auto out = IntegerConstantType(0);                                                    \
    mpz_fun(out._val,                                                                     \
            numerator()._val,                                                             \
            denominator()._val);                                                          \
    return out;                                                                           \
  }                                                                                       \

MK_ROUNDING(floor  , mpz_fdiv_q)
MK_ROUNDING(ceiling, mpz_cdiv_q)

Sign IntegerConstantType::sign() const 
{ auto s = mpz_sgn(_val);
  return s > 0 ? Sign::Pos 
       : s < 0 ? Sign::Neg 
       :         Sign::Zero; }

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
  auto cmp = mpz_cmpabs(n1._val, n2._val);
  if (cmp > 0) return Comparison::GREATER;
  if (cmp < 0) return Comparison::LESS;
  cmp = -mpz_cmp(n1._val, n2._val);
  if (cmp > 0) return Comparison::GREATER;
  if (cmp < 0) return Comparison::LESS;
  else return Comparison::EQUAL;
}

std::string IntegerConstantType::toString() const
{ return to_string(_val); }

///////////////////////
// RationalConstantType
//

RationalConstantType::RationalConstantType(InnerType num, InnerType den)
  : _num(num), _den(den)
{ cannonize(); }

RationalConstantType::RationalConstantType(const std::string& num, const std::string& den)
  : RationalConstantType(InnerType(num), InnerType(den))
{ }

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
  return _den == IntegerConstantType(1);
}

bool RationalConstantType::operator==(const RationalConstantType& o) const
{
  return _num==o._num && _den==o._den;
}

void init_mpq(mpq_t out, mpz_t const num, mpz_t const den) {
  mpq_init(out);
  mpq_set_num(out, num);
  mpq_set_den(out, den);
  mpq_canonicalize(out);
}

void init_mpq(mpq_t out, RationalConstantType const& q) 
{ init_mpq(out, q._num._val, q._den._val); }

// TODO use mpq as repr for Rationals
bool RationalConstantType::operator>(const RationalConstantType& o) const
{
  mpq_t l, r;
  init_mpq(l, *this);
  init_mpq(r, o);
  auto res = mpq_cmp(l, r) > 0;
  mpq_clear(l);
  mpq_clear(r);
  return res;
}

std::string RationalConstantType::toString() const
{ return Lib::toString(*this); }

/**
 * Ensure the GCD of numerator and denominator is 1, and the only
 * number that may be negative is numerator
 */
void RationalConstantType::cannonize()
{
  // TODO faster (?)
  mpq_t q;
  init_mpq(q, *this);
  auto den_ref = mpq_denref(q);
  auto num_ref = mpq_numref(q);
  mpz_swap(_num._val, num_ref);
  mpz_swap(_den._val, den_ref);
  mpq_clear(q);
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

bool RealConstantType::parseDouble(const std::string& num, RationalConstantType& res)
{

  std::string newNum;
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


RealConstantType::RealConstantType(const std::string& number)
  : RealConstantType()
{

  RationalConstantType value;
  if (parseDouble(number, value))  {
    *this = RealConstantType(std::move(value));
    return;
  } else {
    throw UserErrorException("invalid decimal literal");
  }
}

std::string RealConstantType::toNiceString() const
{
  return toString();
}

size_t IntegerConstantType::hash() const {
  return std::hash<decltype(mpz_get_si(_val))>{}(mpz_get_si(_val));
}

size_t RationalConstantType::hash() const {
  return (denominator().hash() << 1) ^ numerator().hash();
}

size_t RealConstantType::hash() const {
  return (denominator().hash() << 1) ^ numerator().hash();
}

} // namespace Kernel

