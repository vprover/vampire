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

  // double numDbl;
  // if (!Int::stringToDouble(number, numDbl)) {
  //   throw MachineArithmeticException();
  // }
  // InnerType denominator = 1;
  // while(::floor(numDbl)!=numDbl) {
  //   denominator = denominator*10;
  //   numDbl *= 10;
  // }
  //
  // if (numDbl > numeric_limits<InnerType::InnerType>::max() ||
  //     numDbl < numeric_limits<InnerType::InnerType>::min()) {
  //   //the numerator part of double doesn't fit inside the inner integer type
  //   throw MachineArithmeticException();
  // }
  //
  // InnerType::InnerType numerator = static_cast<InnerType::InnerType>(numDbl);
  // // the test below should now never trigger (thanks to the one above), but we include it to preserve the original semantics
  // if (numerator!=numDbl) {
  //   //the numerator part of double doesn't fit inside the inner integer type
  //   throw MachineArithmeticException();
  // }
  // init(numerator, denominator);
}

vstring RealConstantType::toNiceString() const
{
  return toString();
  // if (denominator().toInner() == 1) {
  //   return Lib::toString(numerator(), ".0");
  // }
  // mpf_class fl(numerator().toInner());
  // fl /= denominator().toInner();
  // BYPASSING_ALLOCATOR;
  // return vstring(fl.get_str());
  //return toString();
}

/////////////////
// Theory
//

Theory Theory::theory_obj;  // to facilitate destructor call at deinitization
Theory::Tuples Theory::tuples_obj;

Theory* theory = &Theory::theory_obj;
Theory::Tuples* theory_tuples = &Theory::tuples_obj;

/**
 * Accessor for the singleton instance of the Theory class.
 */
Theory* Theory::instance()
{
  return theory;
}

Theory::Tuples* Theory::tuples()
{
  return theory_tuples;
}

/**
 * Constructor of the Theory object
 *
 * The constructor is private, since Theory is a singleton class.
 */
Theory::Theory()
{

}

/**
 * Return arity of the symbol that is interpreted by Interpretation
 * @b i.
 */
unsigned Theory::getArity(Interpretation i)
{
  CALL("Signature::InterpretedSymbol::getArity");
  ASS_L(i,INVALID_INTERPRETATION);

  switch(i) {
  case INT_IS_INT:
  case INT_IS_RAT:
  case INT_IS_REAL:
  case RAT_IS_INT:
  case RAT_IS_RAT:
  case RAT_IS_REAL:
  case REAL_IS_INT:
  case REAL_IS_RAT:
  case REAL_IS_REAL:

  case INT_TO_INT:
  case INT_TO_RAT:
  case INT_TO_REAL:
  case RAT_TO_INT:
  case RAT_TO_RAT:
  case RAT_TO_REAL:
  case REAL_TO_INT:
  case REAL_TO_RAT:
  case REAL_TO_REAL:

  case INT_SUCCESSOR:
  case INT_UNARY_MINUS:
  case RAT_UNARY_MINUS:
  case REAL_UNARY_MINUS:

  case INT_FLOOR:
  case INT_CEILING:
  case INT_TRUNCATE:
  case INT_ROUND:
  case INT_ABS:

  case RAT_FLOOR:
  case RAT_CEILING:
  case RAT_TRUNCATE:
  case RAT_ROUND:

  case REAL_FLOOR:
  case REAL_CEILING:
  case REAL_TRUNCATE:
  case REAL_ROUND:

    return 1;

  case EQUAL:

  case INT_GREATER:
  case INT_GREATER_EQUAL:
  case INT_LESS:
  case INT_LESS_EQUAL:
  case INT_DIVIDES:

  case RAT_GREATER:
  case RAT_GREATER_EQUAL:
  case RAT_LESS:
  case RAT_LESS_EQUAL:

  case REAL_GREATER:
  case REAL_GREATER_EQUAL:
  case REAL_LESS:
  case REAL_LESS_EQUAL:

  case INT_PLUS:
  case INT_MINUS:
  case INT_MULTIPLY:
  case INT_QUOTIENT_E:
  case INT_QUOTIENT_T:
  case INT_QUOTIENT_F:
  case INT_REMAINDER_E:
  case INT_REMAINDER_T:
  case INT_REMAINDER_F:

  case RAT_PLUS:
  case RAT_MINUS:
  case RAT_MULTIPLY:
  case RAT_QUOTIENT:
  case RAT_QUOTIENT_E:
  case RAT_QUOTIENT_T:
  case RAT_QUOTIENT_F:
  case RAT_REMAINDER_E:
  case RAT_REMAINDER_T:
  case RAT_REMAINDER_F:

  case REAL_PLUS:
  case REAL_MINUS:
  case REAL_MULTIPLY:
  case REAL_QUOTIENT:
  case REAL_QUOTIENT_E:
  case REAL_QUOTIENT_T:
  case REAL_QUOTIENT_F:
  case REAL_REMAINDER_E:
  case REAL_REMAINDER_T:
  case REAL_REMAINDER_F:

  case ARRAY_SELECT:
  case ARRAY_BOOL_SELECT:

    return 2;
          
  case ARRAY_STORE:

    return 3;
          
  default:
    ASSERTION_VIOLATION_REP(i);
  }
}

/**
 * Return true iff the symbol that is interpreted by Interpretation
 * is a function (false is returned for predicates)
 */
bool Theory::isFunction(Interpretation i)
{
  CALL("Signature::InterpretedSymbol::isFunction");
  ASS_L(i,INVALID_INTERPRETATION);

  switch(i) {
  case INT_TO_INT:
  case INT_TO_RAT:
  case INT_TO_REAL:
  case RAT_TO_INT:
  case RAT_TO_RAT:
  case RAT_TO_REAL:
  case REAL_TO_INT:
  case REAL_TO_RAT:
  case REAL_TO_REAL:

  case INT_SUCCESSOR:
  case INT_UNARY_MINUS:
  case RAT_UNARY_MINUS:
  case REAL_UNARY_MINUS:

  case INT_PLUS:
  case INT_MINUS:
  case INT_MULTIPLY:
  case INT_QUOTIENT_E:
  case INT_QUOTIENT_T:
  case INT_QUOTIENT_F:
  case INT_REMAINDER_E:
  case INT_REMAINDER_T:
  case INT_REMAINDER_F:
  case INT_FLOOR:
  case INT_CEILING:
  case INT_TRUNCATE:
  case INT_ROUND:
  case INT_ABS:

  case RAT_PLUS:
  case RAT_MINUS:
  case RAT_MULTIPLY:
  case RAT_QUOTIENT:
  case RAT_QUOTIENT_E:
  case RAT_QUOTIENT_T:
  case RAT_QUOTIENT_F:
  case RAT_REMAINDER_E:
  case RAT_REMAINDER_T:
  case RAT_REMAINDER_F:
  case RAT_FLOOR:
  case RAT_CEILING:
  case RAT_TRUNCATE:
  case RAT_ROUND:

  case REAL_PLUS:
  case REAL_MINUS:
  case REAL_MULTIPLY:
  case REAL_QUOTIENT:
  case REAL_QUOTIENT_E:
  case REAL_QUOTIENT_T:
  case REAL_QUOTIENT_F:
  case REAL_REMAINDER_E:
  case REAL_REMAINDER_T:
  case REAL_REMAINDER_F:
  case REAL_FLOOR:
  case REAL_CEILING:
  case REAL_TRUNCATE:
  case REAL_ROUND:
          
  case ARRAY_SELECT:
  case ARRAY_STORE:

    return true;

  case EQUAL:

  case INT_GREATER:
  case INT_GREATER_EQUAL:
  case INT_LESS:
  case INT_LESS_EQUAL:
  case INT_DIVIDES:

  case RAT_GREATER:
  case RAT_GREATER_EQUAL:
  case RAT_LESS:
  case RAT_LESS_EQUAL:

  case REAL_GREATER:
  case REAL_GREATER_EQUAL:
  case REAL_LESS:
  case REAL_LESS_EQUAL:

  case INT_IS_INT:
  case INT_IS_RAT:
  case INT_IS_REAL:
  case RAT_IS_INT:
  case RAT_IS_RAT:
  case RAT_IS_REAL:
  case REAL_IS_INT:
  case REAL_IS_RAT:
  case REAL_IS_REAL:

  case ARRAY_BOOL_SELECT:

    return false;

  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return true iff the symbol that is interpreted by Interpretation
 * is inequality predicate
 */
bool Theory::isInequality(Interpretation i)
{
  CALL("Signature::InterpretedSymbol::isInequality");
  ASS_L(i,INVALID_INTERPRETATION);

  switch(i) {
  case INT_GREATER:
  case INT_GREATER_EQUAL:
  case INT_LESS:
  case INT_LESS_EQUAL:
  case RAT_GREATER:
  case RAT_GREATER_EQUAL:
  case RAT_LESS:
  case RAT_LESS_EQUAL:
  case REAL_GREATER:
  case REAL_GREATER_EQUAL:
  case REAL_LESS:
  case REAL_LESS_EQUAL:
    return true;
  default:
    return false;
  }
  ASSERTION_VIOLATION;
}

/**
 * Return true if interpreted operation @c i has all arguments and
 * (in case of a function) the result type of the same sort.
 * For such operation the @c getOperationSort() function can be
 * called.
 */
bool Theory::hasSingleSort(Interpretation i)
{
  CALL("Theory::hasSingleSort");

  switch(i) {
  case EQUAL:  // This not SingleSort because we don't know the sorts of its args
  case INT_TO_RAT:
  case INT_TO_REAL:
  case RAT_TO_INT:
  case RAT_TO_REAL:
  case REAL_TO_INT:
  case REAL_TO_RAT:

  case ARRAY_SELECT:
  case ARRAY_BOOL_SELECT:
  case ARRAY_STORE:

    return false;
  default:
    return true;
  }
}

bool Theory::isPolymorphic(Interpretation i)
{
  CALL("Theory::isPolymorphic");

  if (i >= numberOfFixedInterpretations()) { // indexed are all polymorphic (for now)
    return true;
  }

  switch(i) {
  case EQUAL:
  case ARRAY_SELECT:
  case ARRAY_BOOL_SELECT:
  case ARRAY_STORE:

    return true;
  default:
    return false;
  }
}

/**
 * This function can be called for operations for which  the
 * function @c hasSingleSort returns true
 */
TermList Theory::getOperationSort(Interpretation i)
{
  CALL("Theory::getOperationSort");

  ASS(hasSingleSort(i));
  ASS_L(i,INVALID_INTERPRETATION);
  ASS(!isPolymorphic(i));

  switch(i) {
  case INT_GREATER:
  case INT_GREATER_EQUAL:
  case INT_LESS:
  case INT_LESS_EQUAL:
  case INT_DIVIDES:
  case INT_SUCCESSOR:
  case INT_UNARY_MINUS:
  case INT_PLUS:
  case INT_MINUS:
  case INT_MULTIPLY:
  case INT_QUOTIENT_E:
  case INT_QUOTIENT_T:
  case INT_QUOTIENT_F:
  case INT_REMAINDER_E:
  case INT_REMAINDER_T:
  case INT_REMAINDER_F:
  case INT_FLOOR:
  case INT_CEILING:
  case INT_TRUNCATE:
  case INT_ROUND:
  case INT_ABS:

  case INT_TO_INT:
  case INT_IS_INT:
  case INT_IS_RAT:
  case INT_IS_REAL:
    return AtomicSort::intSort();

  case RAT_UNARY_MINUS:
  case RAT_PLUS:
  case RAT_MINUS:
  case RAT_MULTIPLY:
  case RAT_QUOTIENT:
  case RAT_QUOTIENT_E:
  case RAT_QUOTIENT_T:
  case RAT_QUOTIENT_F:
  case RAT_REMAINDER_E:
  case RAT_REMAINDER_T:
  case RAT_REMAINDER_F:
  case RAT_FLOOR:
  case RAT_CEILING:
  case RAT_TRUNCATE:
  case RAT_ROUND:
  case RAT_GREATER:
  case RAT_GREATER_EQUAL:
  case RAT_LESS:
  case RAT_LESS_EQUAL:

  case RAT_TO_RAT:
  case RAT_IS_INT:
  case RAT_IS_RAT:
  case RAT_IS_REAL:
    return AtomicSort::rationalSort();

  case REAL_UNARY_MINUS:
  case REAL_PLUS:
  case REAL_MINUS:
  case REAL_MULTIPLY:
  case REAL_QUOTIENT:
  case REAL_QUOTIENT_E:
  case REAL_QUOTIENT_T:
  case REAL_QUOTIENT_F:
  case REAL_REMAINDER_E:
  case REAL_REMAINDER_T:
  case REAL_REMAINDER_F:
  case REAL_FLOOR:
  case REAL_CEILING:
  case REAL_TRUNCATE:
  case REAL_ROUND:
  case REAL_GREATER:
  case REAL_GREATER_EQUAL:
  case REAL_LESS:
  case REAL_LESS_EQUAL:

  case REAL_TO_REAL:
  case REAL_IS_INT:
  case REAL_IS_RAT:
  case REAL_IS_REAL:
    return AtomicSort::realSort();
    
  default:
    ASSERTION_VIOLATION;
  }
}

bool Theory::isConversionOperation(Interpretation i)
{
  CALL("Theory::isConversionOperation");

  //we do not include operations as INT_TO_INT here because they actually
  //don't convert anything (they're identities)
  switch(i) {
  case INT_TO_RAT:
  case INT_TO_REAL:
  case RAT_TO_INT:
  case RAT_TO_REAL:
  case REAL_TO_INT:
  case REAL_TO_RAT:
    return true;
  default:
    return false;
  }
}
bool Theory::isLinearOperation(Interpretation i)
{
  CALL("Theory::isLinearOperation");

  switch(i) {
  case INT_UNARY_MINUS:
  case INT_PLUS:
  case INT_MINUS:
  case RAT_UNARY_MINUS:
  case RAT_PLUS:
  case RAT_MINUS:
  case REAL_UNARY_MINUS:
  case REAL_PLUS:
  case REAL_MINUS:
    return true;
  default:
    return false;
  }
}
bool Theory::isNonLinearOperation(Interpretation i)
{
  CALL("Theory::isNonLinearOperation");

  switch(i) {
  case INT_MULTIPLY:
  case INT_QUOTIENT_E:
  case INT_QUOTIENT_T:
  case INT_QUOTIENT_F:
  case INT_REMAINDER_E:
  case INT_REMAINDER_T:
  case INT_REMAINDER_F:
  case RAT_MULTIPLY:
  case RAT_QUOTIENT:
  case RAT_QUOTIENT_E:
  case RAT_QUOTIENT_T:
  case RAT_QUOTIENT_F:
  case RAT_REMAINDER_E:
  case RAT_REMAINDER_T:
  case RAT_REMAINDER_F:
  case REAL_MULTIPLY:
  case REAL_QUOTIENT:
  case REAL_QUOTIENT_E:
  case REAL_QUOTIENT_T:
  case REAL_QUOTIENT_F:
  case REAL_REMAINDER_E:
  case REAL_REMAINDER_T:
  case REAL_REMAINDER_F:
    return true;
  default:
    return false;
  }
}

bool Theory::isPartiallyInterpretedFunction(Term* t) {
  CALL("Theory::isPartiallyInterpretedFunction(Term* t)")
  auto f = t->functor();
  ASS(!t->isLiteral())
  if(theory->isInterpretedFunction(f)) {
    switch (theory->interpretFunction(f)) {
      case Theory::INT_QUOTIENT_E:
      case Theory::INT_QUOTIENT_T:
      case Theory::INT_QUOTIENT_F:
      case Theory::INT_REMAINDER_E:
      case Theory::INT_REMAINDER_T:
      case Theory::INT_REMAINDER_F:
      case Theory::RAT_QUOTIENT:
      case Theory::RAT_QUOTIENT_E:
      case Theory::RAT_QUOTIENT_T:
      case Theory::RAT_QUOTIENT_F:
      case Theory::RAT_REMAINDER_E:
      case Theory::RAT_REMAINDER_T:
      case Theory::RAT_REMAINDER_F:
      case Theory::REAL_QUOTIENT:
      case Theory::REAL_QUOTIENT_E:
      case Theory::REAL_QUOTIENT_T:
      case Theory::REAL_QUOTIENT_F:
      case Theory::REAL_REMAINDER_E:
      case Theory::REAL_REMAINDER_T:
      case Theory::REAL_REMAINDER_F:
        return true;

      default:
        return false;
    }
  } else {
    auto sym = env.signature->getFunction(t->functor());
    if (isInterpretedNumber(t)) {
      return false;
    } else if (sym->termAlgebraCons()) {
      return false;
    } else if (sym->termAlgebraDest()) {
      return true;
    } else {
      ASSERTION_VIOLATION_REP(t)
    }
  }
}

bool Theory::partiallyDefinedFunctionUndefinedForArgs(Term* t) {
  CALL("Theory::partiallyDefinedFunctionUndefinedForArgs(Term* t)")
  ASS(isPartiallyInterpretedFunction(t))
  auto f = t->functor();
  ASS(!t->isLiteral())
  if(theory->isInterpretedFunction(f)) {
    switch (theory->interpretFunction(f)) {
      case Theory::INT_QUOTIENT_E:
      case Theory::INT_QUOTIENT_T:
      case Theory::INT_QUOTIENT_F:
      case Theory::INT_REMAINDER_E:
      case Theory::INT_REMAINDER_T:
      case Theory::INT_REMAINDER_F:
        return IntTraits::isZero(t->termArg(1));
      case Theory::RAT_QUOTIENT:
      case Theory::RAT_QUOTIENT_E:
      case Theory::RAT_QUOTIENT_T:
      case Theory::RAT_QUOTIENT_F:
      case Theory::RAT_REMAINDER_E:
      case Theory::RAT_REMAINDER_T:
      case Theory::RAT_REMAINDER_F:
        return RatTraits::isZero(t->termArg(1));
      case Theory::REAL_QUOTIENT:
      case Theory::REAL_QUOTIENT_E:
      case Theory::REAL_QUOTIENT_T:
      case Theory::REAL_QUOTIENT_F:
      case Theory::REAL_REMAINDER_E:
      case Theory::REAL_REMAINDER_T:
      case Theory::REAL_REMAINDER_F:
        return RealTraits::isZero(t->termArg(1));
      default:
        return false;
    }
  } else {
    auto sym = env.signature->getFunction(t->functor());
    if (sym->termAlgebraCons()) {
      return false;
    } else {
      ASS(sym->termAlgebraDest());
      auto arg = t->termArg(0);
      if (arg.isVar())  {
        return false;
      } else {
        ASS(arg.isTerm());
        auto fn = arg.term()->functor();
        // auto argSym = env.signature->getFunction(fn);
        auto ctor = env.signature->getTermAlgebraConstructor(fn);
        if (ctor == nullptr) {
          return false;
        } else {
          for (unsigned i = 0; i < ctor->arity(); i++) {
            if (ctor->destructorFunctor(i) == f) {
              return true;
            }
          }
          // destructor belongs to different constructor
          return false;
        }
      }
    }
  }
}


/**
 * Get the number of the skolem function symbol used in the clause form of the
 * array extensionality axiom (of particular sort).
 *
 * select(X,sk(X,Y)) != select(Y,sk(X,Y)) | X = Y
 * 
 * If the symbol does not exist yet, it is added to the signature. We use 0 to
 * represent that the symbol not yet exists, assuming that at call time of this
 * method, at least the array function are already in the signature.
 *
 * We want to have this function available e.g. in simplification rules.
 */
unsigned Theory::getArrayExtSkolemFunction(TermList sort) {
  CALL("Theory::getArrayExtSkolemFunction")
  ASS(sort.isArraySort());

  if(_arraySkolemFunctions.find(sort)){
    return _arraySkolemFunctions.get(sort);
  }

  TermList indexSort = SortHelper::getIndexSort(sort);
  TermList params[] = {sort, sort};
  unsigned skolemFunction = Shell::Skolem::addSkolemFunction(2, 0, params, indexSort, "arrayDiff");

  _arraySkolemFunctions.insert(sort,skolemFunction);

  return skolemFunction; 
}

unsigned Theory::Tuples::getFunctor(unsigned arity, TermList* sorts) {
  CALL("Theory::Tuples::getFunctor(unsigned arity, unsigned* sorts)");
  return getFunctor(AtomicSort::tupleSort(arity, sorts));
}

unsigned Theory::Tuples::getFunctor(TermList tupleSort) {
  CALL("Theory::Tuples::getFunctor(unsigned tupleSort)");

  ASS_REP(tupleSort.isTupleSort(), tupleSort.toString());

  unsigned  arity = tupleSort.term()->arity();
  TermList* sorts = tupleSort.term()->args();

  theory->defineTupleTermAlgebra(arity, sorts);
  ASS(env.signature->isTermAlgebraSort(tupleSort));
  Shell::TermAlgebra* ta = env.signature->getTermAlgebraOfSort(tupleSort);

  return ta->constructor(0)->functor();
}

bool Theory::Tuples::isFunctor(unsigned functor) {
  CALL("Theory::Tuples::isFunctor(unsigned)");
  TermList tupleSort = env.signature->getFunction(functor)->fnType()->result();
  return tupleSort.isTupleSort();
}

unsigned Theory::Tuples::getProjectionFunctor(unsigned proj, TermList tupleSort) {
  CALL("Theory::Tuples::getProjectionFunctor");

  ASS_REP(tupleSort.isTupleSort(), tupleSort.toString());

  unsigned  arity = tupleSort.term()->arity();
  TermList* sorts = tupleSort.term()->args();

  theory->defineTupleTermAlgebra(arity, sorts);
  ASS(env.signature->isTermAlgebraSort(tupleSort));
  Shell::TermAlgebra* ta = env.signature->getTermAlgebraOfSort(tupleSort);

  Shell::TermAlgebraConstructor* c = ta->constructor(0);

  ASS_NEQ(proj, c->arity());

  return c->destructorFunctor(proj);
}

// TODO: replace with a constant time algorithm
bool Theory::Tuples::findProjection(unsigned projFunctor, bool isPredicate, unsigned &proj) {
  CALL("Theory::Tuples::findProjection");
 
  OperatorType* projType = isPredicate ? env.signature->getPredicate(projFunctor)->predType()
                                       : env.signature->getFunction(projFunctor)->fnType();

  if (projType->arity() != 1) {
    return false;
  }

  TermList tupleSort = projType->arg(0);

  if (!tupleSort.isTupleSort()) {
    return false;
  }

  if (!env.signature->isTermAlgebraSort(tupleSort)) {
    return false;
  }

  Shell::TermAlgebraConstructor* c = env.signature->getTermAlgebraOfSort(tupleSort)->constructor(0);
  for (unsigned i = 0; i < c->arity(); i++) {
    if (projFunctor == c->destructorFunctor(i)) {
      proj = i;
      return true;
    }
  }

  return false;
}


/**
 * This function creates a type for converion function @c i.
 *
 * @c i must be a type conversion operation.
 */
OperatorType* Theory::getConversionOperationType(Interpretation i)
{
  CALL("Theory::getConversionOperationType");

  TermList from, to;
  switch(i) {
  case INT_TO_RAT:
    from = AtomicSort::intSort();
    to = AtomicSort::rationalSort();
    break;
  case INT_TO_REAL:
    from = AtomicSort::intSort();
    to = AtomicSort::realSort();
    break;
  case RAT_TO_INT:
    from = AtomicSort::rationalSort();
    to = AtomicSort::intSort();
    break;
  case RAT_TO_REAL:
    from = AtomicSort::rationalSort();
    to = AtomicSort::realSort();
    break;
  case REAL_TO_INT:
    from = AtomicSort::realSort();
    to = AtomicSort::intSort();
    break;
  case REAL_TO_RAT:
    from = AtomicSort::realSort();
    to = AtomicSort::rationalSort();
    break;
  default:
    ASSERTION_VIOLATION;
  }
  return OperatorType::getFunctionType({from}, to);
}

vstring Theory::getInterpretationName(Interpretation interp) {
  CALL("Theory::getInterpretationName");

  switch (interp) {
    case INT_SUCCESSOR:
      //this one is not according the TPTP arithmetic (it doesn't have successor)
      return "$successor";
    case INT_DIVIDES:
      return "$divides";
    case INT_UNARY_MINUS:
    case RAT_UNARY_MINUS:
    case REAL_UNARY_MINUS:
      return "$uminus";
    case INT_PLUS:
    case RAT_PLUS:
    case REAL_PLUS:
      return "$sum";
    case INT_MINUS:
    case RAT_MINUS:
    case REAL_MINUS:
      return "$difference";
    case INT_MULTIPLY:
    case RAT_MULTIPLY:
    case REAL_MULTIPLY:
      return "$product";
    case INT_GREATER:
    case RAT_GREATER:
    case REAL_GREATER:
      return "$greater";
    case INT_GREATER_EQUAL:
    case RAT_GREATER_EQUAL:
    case REAL_GREATER_EQUAL:
      return "$greatereq";
    case INT_LESS:
    case RAT_LESS:
    case REAL_LESS:
      return "$less";
    case INT_LESS_EQUAL:
    case RAT_LESS_EQUAL:
    case REAL_LESS_EQUAL:
      return "$lesseq";
    case INT_IS_INT:
    case RAT_IS_INT:
    case REAL_IS_INT:
      return "$is_int";
    case INT_IS_RAT:
    case RAT_IS_RAT:
    case REAL_IS_RAT:
      return "$is_rat";
    case INT_IS_REAL:
    case RAT_IS_REAL:
    case REAL_IS_REAL:
      return "$is_real";
    case INT_TO_INT:
    case RAT_TO_INT:
    case REAL_TO_INT:
      return "$to_int";
    case INT_TO_RAT:
    case RAT_TO_RAT:
    case REAL_TO_RAT:
      return "$to_rat";
    case INT_TO_REAL:
    case RAT_TO_REAL:
    case REAL_TO_REAL:
      return "$to_real";
    case INT_ABS:
      return "$abs";
    case INT_QUOTIENT_E:
    case RAT_QUOTIENT_E:
    case REAL_QUOTIENT_E:
      return "$quotient_e";
    case INT_QUOTIENT_T:
    case RAT_QUOTIENT_T:
    case REAL_QUOTIENT_T:
      return "$quotient_t";
    case INT_QUOTIENT_F:
    case RAT_QUOTIENT_F:
    case REAL_QUOTIENT_F:
      return "$quotient_f";
    case INT_REMAINDER_T:
    case RAT_REMAINDER_T:
    case REAL_REMAINDER_T:
      return "$remainder_t";
    case INT_REMAINDER_F:
    case RAT_REMAINDER_F:
    case REAL_REMAINDER_F:
      return "$remainder_f";
    case INT_REMAINDER_E:
    case RAT_REMAINDER_E:
    case REAL_REMAINDER_E:
      return "$remainder_e";
    case RAT_QUOTIENT:
    case REAL_QUOTIENT:
      return "$quotient";
    case INT_TRUNCATE:
    case RAT_TRUNCATE:
    case REAL_TRUNCATE:
      return "truncate";
    case INT_FLOOR:
    case RAT_FLOOR:
    case REAL_FLOOR:
      return "floor";
    case INT_CEILING:
    case RAT_CEILING:
    case REAL_CEILING:
      return "ceiling";
    case ARRAY_SELECT:
    case ARRAY_BOOL_SELECT:
      return "$select";
    case ARRAY_STORE:
      return "$store";
    default:
      ASSERTION_VIOLATION_REP(interp);
  }
}

OperatorType* Theory::getArrayOperatorType(TermList arraySort, Interpretation i) {
  CALL("Theory::getArrayOperatorType");
  ASS(arraySort.isArraySort());

  TermList indexSort = SortHelper::getIndexSort(arraySort);
  TermList innerSort = SortHelper::getInnerSort(arraySort);

  switch (i) {
    case Interpretation::ARRAY_SELECT:
      return OperatorType::getFunctionType({ arraySort, indexSort }, innerSort);

    case Interpretation::ARRAY_BOOL_SELECT:
      return OperatorType::getPredicateType({ arraySort, indexSort });

    case Interpretation::ARRAY_STORE:
      return OperatorType::getFunctionType({ arraySort, indexSort, innerSort }, arraySort);

    default:
      ASSERTION_VIOLATION;
  }
}

/**
 * Return type of the function representing interpreted function/predicate @c i.
 */
OperatorType* Theory::getNonpolymorphicOperatorType(Interpretation i)
{
  CALL("Theory::getNonpolymorphicOperationType");
  ASS(!isPolymorphic(i));

  if (isConversionOperation(i)) {
    return getConversionOperationType(i);
  }

  ASS(hasSingleSort(i));
  TermList sort = getOperationSort(i);

  unsigned arity = getArity(i);

  static DArray<TermList> domainSorts;
  domainSorts.init(arity, sort);

  if (isFunction(i)) {
    return OperatorType::getFunctionType(arity, domainSorts.array(), sort);
  } else {
    return OperatorType::getPredicateType(arity, domainSorts.array());
  }
}

void Theory::defineTupleTermAlgebra(unsigned arity, TermList* sorts) {
  CALL("Signature::defineTupleTermAlgebra");

  TermList tupleSort = AtomicSort::tupleSort(arity, sorts);

  if (env.signature->isTermAlgebraSort(tupleSort)) {
    return;
  }

  unsigned functor = env.signature->addFreshFunction(arity, "tuple");
  OperatorType* tupleType = OperatorType::getFunctionType(arity, sorts, tupleSort);
  env.signature->getFunction(functor)->setType(tupleType);
  env.signature->getFunction(functor)->markTermAlgebraCons();

  Array<unsigned> destructors(arity);
  for (unsigned i = 0; i < arity; i++) {
    TermList projSort = sorts[i];
    unsigned destructor;
    Signature::Symbol* destSym;
    if (projSort == AtomicSort::boolSort()) {
      destructor = env.signature->addFreshPredicate(1, "proj");
      destSym = env.signature->getPredicate(destructor);
      destSym->setType(OperatorType::getPredicateType({ tupleSort }));
    } else {
      destructor = env.signature->addFreshFunction(1, "proj");
      destSym = env.signature->getFunction(destructor);
      destSym->setType(OperatorType::getFunctionType({ tupleSort }, projSort));
    }
    destSym->markTermAlgebraDest();
    destructors[i] = destructor;
  }

  Shell::TermAlgebraConstructor* constructor = new Shell::TermAlgebraConstructor(functor, destructors);

  Shell::TermAlgebraConstructor* constructors[] = { constructor };
  env.signature->addTermAlgebra(new Shell::TermAlgebra(tupleSort, 1, constructors, false));
}

bool Theory::isInterpretedConstant(unsigned func)
{
  CALL("Theory::isInterpretedConstant");

  if (func>=Term::SPECIAL_FUNCTOR_LOWER_BOUND) {
    return false;
  }

  return env.signature->getFunction(func)->interpreted() && env.signature->functionArity(func)==0;
}

/**
 * Return true iff @b t is an interpreted constant
 */
bool Theory::isInterpretedConstant(Term* t)
{
  CALL("Theory::isInterpretedConstant(Term*)");

  if (t->isSpecial()) { return false; }

  return t->numTermArguments()==0 && env.signature->getFunction(t->functor())->interpreted();
}

/**
 * Return true iff @b t is an interpreted constant
 */
bool Theory::isInterpretedConstant(TermList t)
{
  CALL("Theory::isInterpretedConstant(TermList)");

  return t.isTerm() && isInterpretedConstant(t.term());
}

/**
 * Return true iff @b t is a constant with a numerical interpretation
 */
bool Theory::isInterpretedNumber(Term* t)
{
  CALL("Theory::isInterpretedNumber(TermList)");

  return isInterpretedConstant(t) && env.signature->getFunction(t->functor())->interpretedNumber();
}

/**
 * Return true iff @b t is a constant with a numerical interpretation
 */
bool Theory::isInterpretedNumber(TermList t)
{
  CALL("Theory::isInterpretedNumber(TermList)");

  return isInterpretedConstant(t) && env.signature->getFunction(t.term()->functor())->interpretedNumber();
}

/**
 * Return true iff @b pred is an interpreted predicate
 */
bool Theory::isInterpretedPredicate(unsigned pred)
{
  CALL("Theory::isInterpretedPredicate(unsigned)");

  return env.signature->getPredicate(pred)->interpreted();
}

/**
 * Return true iff @b lit has an interpreted predicate
 */
bool Theory::isInterpretedEquality(Literal* lit)
{
  CALL("Theory::isInterpretedEquality");

  if(lit->isEquality()){
    TermList srt = SortHelper::getEqualityArgumentSort(lit);
    // TODO should this return true for datatypes, arrays, etc?
    return (srt == AtomicSort::intSort() || srt == AtomicSort::realSort() || srt == AtomicSort::rationalSort());
  } else {
    return false;
  }
}

/**
 * Return true iff @b lit has an interpreted predicate interpreted
 * as @b itp
 */
bool Theory::isInterpretedPredicate(Literal* lit)
{
  CALL("Theory::isInterpretedPredicate/1");

  return env.signature->getPredicate(lit->functor())->interpreted();
}


/**
 * Return true iff @b lit has an interpreted predicate interpreted
 * as @b itp
 */
bool Theory::isInterpretedPredicate(Literal* lit, Interpretation itp)
{
  CALL("Theory::isInterpretedPredicate/2");

  return isInterpretedPredicate(lit) && interpretPredicate(lit)==itp;
}

bool Theory::isInterpretedFunction(unsigned func)
{
  CALL("Theory::isInterpretedFunction(unsigned)");

  if (func>=Term::SPECIAL_FUNCTOR_LOWER_BOUND) {
    return false;
  }

  return env.signature->getFunction(func)->interpreted() && env.signature->functionArity(func)!=0;
}

bool Theory::isZero(TermList term)
{
  CALL("Theory::isZero");


  IntegerConstantType it;
  if(tryInterpretConstant(term,it) && it.isZero()){ return true; }

  RationalConstantType rtt;
  if(tryInterpretConstant(term,rtt) && rtt.isZero()){ return true; }

  RealConstantType ret;
  if(tryInterpretConstant(term,ret) && ret.isZero()){ return true; }

  return false;
}


/**
 * Return true iff @b t is an interpreted function
 */
bool Theory::isInterpretedFunction(Term* t)
{
  CALL("Theory::isInterpretedFunction(Term*)");

  return isInterpretedFunction(t->functor());
}

/**
 * Return true iff @b t is an interpreted function
 */
bool Theory::isInterpretedFunction(TermList t)
{
  CALL("Theory::isInterpretedFunction(TermList)");

  return t.isTerm() && isInterpretedFunction(t.term());
}

/**
 * Return true iff @b t is an interpreted function interpreted
 * as @b itp
 */
bool Theory::isInterpretedFunction(Term* t, Interpretation itp)
{
  CALL("Theory::isInterpretedFunction(Term*,Interpretation)");

  return isInterpretedFunction(t->functor()) &&
      interpretFunction(t)==itp;
}

/**
 * Return true iff @b t is an interpreted function interpreted
 * as @b itp
 */
bool Theory::isInterpretedFunction(TermList t, Interpretation itp)
{
  CALL("Theory::isInterpretedFunction(TermList,Interpretation)");

  return t.isTerm() && isInterpretedFunction(t.term(), itp);
}


Interpretation Theory::interpretFunction(unsigned func)
{
  CALL("Theory::interpretFunction");
  ASS(isInterpretedFunction(func));

  Signature::InterpretedSymbol* sym =
      static_cast<Signature::InterpretedSymbol*>(env.signature->getFunction(func));

  return sym->getInterpretation();
}

/**
 * Assuming @b t is an interpreted function, return its interpretation
 */
Interpretation Theory::interpretFunction(Term* t)
{
  CALL("Theory::interpretFunction");
  ASS(isInterpretedFunction(t));

  return interpretFunction(t->functor());
}

/**
 * Assuming @b t is an interpreted function, return its interpretation
 */
Interpretation Theory::interpretFunction(TermList t)
{
  CALL("Theory::interpretFunction");
  ASS(t.isTerm());

  return interpretFunction(t.term());
}

Interpretation Theory::interpretPredicate(unsigned pred)
{
  CALL("Theory::interpretPredicate");
  ASS(isInterpretedPredicate(pred));

  Signature::InterpretedSymbol* sym =
      static_cast<Signature::InterpretedSymbol*>(env.signature->getPredicate(pred));

  return sym->getInterpretation();
}

/**
 * Assuming @b lit has an interpreted predicate, return its interpretation.
 * Does not return the interpretation of equality.
 */
Interpretation Theory::interpretPredicate(Literal* lit)
{
  CALL("Theory::interpretPredicate");
  ASS(isInterpretedPredicate(lit->functor()));

  return interpretPredicate(lit->functor());
}

/**
 * Try to interpret the term as an integer constant. If it is an
 * integer constant, return true and save the constant in @c res, otherwise
 * return false.
 * @since 04/05/2013 Manchester
 * @author Andrei Voronkov
 */
bool Theory::tryInterpretConstant(const Term* t, IntegerConstantType& res)
{
  CALL("Theory::tryInterpretConstant(Term*,IntegerConstantType)");

  if (t->numTermArguments() != 0 || t->isSpecial()) {
    return false;
  }
  unsigned func = t->functor();
  return tryInterpretConstant(func, res);
} // Theory::tryInterpretConstant


bool Theory::tryInterpretConstant(unsigned func, IntegerConstantType& res)
{
  Signature::Symbol* sym = env.signature->getFunction(func);
  CALL("Theory::tryInterpretConstant(Term*,IntegerConstantType)");
  if (!sym->integerConstant()) {
    return false;
  }
  res = sym->integerValue();
  return true;
}



/**
 * Try to interpret the term as an rational constant. If it is an
 * rational constant, return true and save the constant in @c res, otherwise
 * return false.
 * @since 04/05/2013 Manchester
 * @author Andrei Voronkov
 */
bool Theory::tryInterpretConstant(const Term* t, RationalConstantType& res)
{
  CALL("Theory::tryInterpretConstant(Term*,RationalConstantType)");

  if (t->numTermArguments() != 0 || t->isSpecial()) {
    return false;
  }
  unsigned func = t->functor();
  return tryInterpretConstant(func, res);
} // Theory::tryInterpretConstant 

bool Theory::tryInterpretConstant(unsigned func, RationalConstantType& res)
{
  Signature::Symbol* sym = env.signature->getFunction(func);
  CALL("Theory::tryInterpretConstant(Term*,RationalConstantType)");
  if (!sym->rationalConstant()) {
    return false;
  }
  res = sym->rationalValue();
  return true;
}


/**
 * Try to interpret the term as a real constant. If it is an
 * real constant, return true and save the constant in @c res, otherwise
 * return false.
 * @since 04/05/2013 Manchester
 * @author Andrei Voronkov
 */
bool Theory::tryInterpretConstant(const Term* t, RealConstantType& res)
{
  CALL("Theory::tryInterpretConstant(Term*,RealConstantType)");

  if (t->numTermArguments() != 0 || t->isSpecial()) {
    return false;
  }
  unsigned func = t->functor();
  return tryInterpretConstant(func, res);
} // // Theory::tryInterpretConstant

bool Theory::tryInterpretConstant(unsigned func, RealConstantType& res)
{
  Signature::Symbol* sym = env.signature->getFunction(func);
  CALL("Theory::tryInterpretConstant(Term*,RealConstantType)");
  if (!sym->realConstant()) {
    return false;
  }
  res = sym->realValue();
  return true;
}

Term* Theory::representConstant(const IntegerConstantType& num)
{
  CALL("Theory::representConstant(const IntegerConstantType&)");

  unsigned func = env.signature->addIntegerConstant(num);
  return Term::create(func, 0, 0);
}

Term* Theory::representConstant(const RationalConstantType& num)
{
  CALL("Theory::representConstant(const RationalConstantType&)");

  unsigned func = env.signature->addRationalConstant(num);
  return Term::create(func, 0, 0);
}

Term* Theory::representConstant(const RealConstantType& num)
{
  CALL("Theory::representConstant(const RealConstantType&)");

  unsigned func = env.signature->addRealConstant(num);
  return Term::create(func, 0, 0);
}

Term* Theory::representIntegerConstant(vstring str)
{
  CALL("Theory::representIntegerConstant");

  try {
    return Theory::instance()->representConstant(IntegerConstantType(str));
  }
  catch(ArithmeticException&) {
    NOT_IMPLEMENTED;
//    bool added;
//    unsigned fnNum = env.signature->addFunction(str, 0, added);
//    if (added) {
//      env.signature->getFunction(fnNum)->setType(new FunctionType(Sorts::SRT_INTEGER));
//      env.signature->addToDistinctGroup(fnNum, Signature::INTEGER_DISTINCT_GROUP);
//    }
//    else {
//      ASS(env.signature->getFunction(fnNum))
//    }
  }
}

Term* Theory::representRealConstant(vstring str)
{
  CALL("Theory::representRealConstant");
  try {
    return Theory::instance()->representConstant(RealConstantType(str));
  } catch(ArithmeticException&) {
    NOT_IMPLEMENTED;
  }
}

/**
 * Register that a predicate pred with a given polarity has the given
 * template. See tryGetInterpretedLaTeXName for explanation of templates 
 */
void Theory::registerLaTeXPredName(unsigned pred, bool polarity, vstring temp)
{
  CALL("Theory::registerPredLaTeXName");
  if(polarity){
    _predLaTeXnamesPos.insert(pred,temp);
  }else{
    _predLaTeXnamesNeg.insert(pred,temp); 
  }
}
/**
 * Register that a function has the given template
 * See tryGetInterpretedLaTeXName for explanation of templates 
 */
void Theory::registerLaTeXFuncName(unsigned func, vstring temp)
{
  CALL("Theory::registerFuncLaTeXName");
  _funcLaTeXnames.insert(func,temp);
}

std::ostream& operator<<(std::ostream& out, Kernel::Theory::Interpretation const& self)
{
  switch(self) {
    case Kernel::Theory::EQUAL: return out << "EQUAL";
    case Kernel::Theory::INT_IS_INT: return out << "INT_IS_INT";
    case Kernel::Theory::INT_IS_RAT: return out << "INT_IS_RAT";
    case Kernel::Theory::INT_IS_REAL: return out << "INT_IS_REAL";
    case Kernel::Theory::INT_GREATER: return out << "INT_GREATER";
    case Kernel::Theory::INT_GREATER_EQUAL: return out << "INT_GREATER_EQUAL";
    case Kernel::Theory::INT_LESS: return out << "INT_LESS";
    case Kernel::Theory::INT_LESS_EQUAL: return out << "INT_LESS_EQUAL";
    case Kernel::Theory::INT_DIVIDES: return out << "INT_DIVIDES";
    case Kernel::Theory::RAT_IS_INT: return out << "RAT_IS_INT";
    case Kernel::Theory::RAT_IS_RAT: return out << "RAT_IS_RAT";
    case Kernel::Theory::RAT_IS_REAL: return out << "RAT_IS_REAL";
    case Kernel::Theory::RAT_GREATER: return out << "RAT_GREATER";
    case Kernel::Theory::RAT_GREATER_EQUAL: return out << "RAT_GREATER_EQUAL";
    case Kernel::Theory::RAT_LESS: return out << "RAT_LESS";
    case Kernel::Theory::RAT_LESS_EQUAL: return out << "RAT_LESS_EQUAL";
    case Kernel::Theory::REAL_IS_INT: return out << "REAL_IS_INT";
    case Kernel::Theory::REAL_IS_RAT: return out << "REAL_IS_RAT";
    case Kernel::Theory::REAL_IS_REAL: return out << "REAL_IS_REAL";
    case Kernel::Theory::REAL_GREATER: return out << "REAL_GREATER";
    case Kernel::Theory::REAL_GREATER_EQUAL: return out << "REAL_GREATER_EQUAL";
    case Kernel::Theory::REAL_LESS: return out << "REAL_LESS";
    case Kernel::Theory::REAL_LESS_EQUAL: return out << "REAL_LESS_EQUAL";
    case Kernel::Theory::INT_SUCCESSOR: return out << "INT_SUCCESSOR";
    case Kernel::Theory::INT_UNARY_MINUS: return out << "INT_UNARY_MINUS";
    case Kernel::Theory::INT_PLUS: return out << "INT_PLUS";
    case Kernel::Theory::INT_MINUS: return out << "INT_MINUS";
    case Kernel::Theory::INT_MULTIPLY: return out << "INT_MULTIPLY";
    case Kernel::Theory::INT_QUOTIENT_E: return out << "INT_QUOTIENT_E";
    case Kernel::Theory::INT_QUOTIENT_T: return out << "INT_QUOTIENT_T";
    case Kernel::Theory::INT_QUOTIENT_F: return out << "INT_QUOTIENT_F";
    case Kernel::Theory::INT_REMAINDER_E: return out << "INT_REMAINDER_E";
    case Kernel::Theory::INT_REMAINDER_T: return out << "INT_REMAINDER_T";
    case Kernel::Theory::INT_REMAINDER_F: return out << "INT_REMAINDER_F";
    case Kernel::Theory::INT_FLOOR: return out << "INT_FLOOR";
    case Kernel::Theory::INT_CEILING: return out << "INT_CEILING";
    case Kernel::Theory::INT_TRUNCATE: return out << "INT_TRUNCATE";
    case Kernel::Theory::INT_ROUND: return out << "INT_ROUND";
    case Kernel::Theory::INT_ABS: return out << "INT_ABS";
    case Kernel::Theory::RAT_UNARY_MINUS: return out << "RAT_UNARY_MINUS";
    case Kernel::Theory::RAT_PLUS: return out << "RAT_PLUS";
    case Kernel::Theory::RAT_MINUS: return out << "RAT_MINUS";
    case Kernel::Theory::RAT_MULTIPLY: return out << "RAT_MULTIPLY";
    case Kernel::Theory::RAT_QUOTIENT: return out << "RAT_QUOTIENT";
    case Kernel::Theory::RAT_QUOTIENT_E: return out << "RAT_QUOTIENT_E";
    case Kernel::Theory::RAT_QUOTIENT_T: return out << "RAT_QUOTIENT_T";
    case Kernel::Theory::RAT_QUOTIENT_F: return out << "RAT_QUOTIENT_F";
    case Kernel::Theory::RAT_REMAINDER_E: return out << "RAT_REMAINDER_E";
    case Kernel::Theory::RAT_REMAINDER_T: return out << "RAT_REMAINDER_T";
    case Kernel::Theory::RAT_REMAINDER_F: return out << "RAT_REMAINDER_F";
    case Kernel::Theory::RAT_FLOOR: return out << "RAT_FLOOR";
    case Kernel::Theory::RAT_CEILING: return out << "RAT_CEILING";
    case Kernel::Theory::RAT_TRUNCATE: return out << "RAT_TRUNCATE";
    case Kernel::Theory::RAT_ROUND: return out << "RAT_ROUND";
    case Kernel::Theory::REAL_UNARY_MINUS: return out << "REAL_UNARY_MINUS";
    case Kernel::Theory::REAL_PLUS: return out << "REAL_PLUS";
    case Kernel::Theory::REAL_MINUS: return out << "REAL_MINUS";
    case Kernel::Theory::REAL_MULTIPLY: return out << "REAL_MULTIPLY";
    case Kernel::Theory::REAL_QUOTIENT: return out << "REAL_QUOTIENT";
    case Kernel::Theory::REAL_QUOTIENT_E: return out << "REAL_QUOTIENT_E";
    case Kernel::Theory::REAL_QUOTIENT_T: return out << "REAL_QUOTIENT_T";
    case Kernel::Theory::REAL_QUOTIENT_F: return out << "REAL_QUOTIENT_F";
    case Kernel::Theory::REAL_REMAINDER_E: return out << "REAL_REMAINDER_E";
    case Kernel::Theory::REAL_REMAINDER_T: return out << "REAL_REMAINDER_T";
    case Kernel::Theory::REAL_REMAINDER_F: return out << "REAL_REMAINDER_F";
    case Kernel::Theory::REAL_FLOOR: return out << "REAL_FLOOR";
    case Kernel::Theory::REAL_CEILING: return out << "REAL_CEILING";
    case Kernel::Theory::REAL_TRUNCATE: return out << "REAL_TRUNCATE";
    case Kernel::Theory::REAL_ROUND: return out << "REAL_ROUND";
    case Kernel::Theory::INT_TO_INT: return out << "INT_TO_INT";
    case Kernel::Theory::INT_TO_RAT: return out << "INT_TO_RAT";
    case Kernel::Theory::INT_TO_REAL: return out << "INT_TO_REAL";
    case Kernel::Theory::RAT_TO_INT: return out << "RAT_TO_INT";
    case Kernel::Theory::RAT_TO_RAT: return out << "RAT_TO_RAT";
    case Kernel::Theory::RAT_TO_REAL: return out << "RAT_TO_REAL";
    case Kernel::Theory::REAL_TO_INT: return out << "REAL_TO_INT";
    case Kernel::Theory::REAL_TO_RAT: return out << "REAL_TO_RAT";
    case Kernel::Theory::REAL_TO_REAL: return out << "REAL_TO_REAL";
    case Kernel::Theory::ARRAY_SELECT: return out << "ARRAY_SELECT";
    case Kernel::Theory::ARRAY_BOOL_SELECT: return out << "ARRAY_BOOL_SELECT";
    case Kernel::Theory::ARRAY_STORE: return out << "ARRAY_STORE";
    case Kernel::Theory::INVALID_INTERPRETATION: return out << "INVALID_INTERPRETATION";
  }
  ASSERTION_VIOLATION
}
/**
 * We try and get a LaTeX special name for an interpeted function/predicate.
 * Note: the functions may not necessarily be interpreted in the sense that we treat
 *       them as interpreted in Vampire. They are just called that here as we have an
 *       interpretation for them. So we can have LaTeX symbols for any predicate or
 *       function if they are recorded e.g. skolem functions are recorded in Signature.
 *
 * See Shell/LaTeX for usage.
 *
 * Polarity only makes sense if pred=true
 *
 * First we look in the recorded templates and if one is not found we fallback to the
 * default templates for known interprted functions. Note that in most cases the known
 * interpreted functions will use these defaults.
 *
 * A template is a string with "ai" representing parameter i. These will be
 * replaced by the actual parameters elsewhere. For example, the template for 
 * not greater or equal to is "a0 \not \geq a1"
 */
vstring Theory::tryGetInterpretedLaTeXName(unsigned func, bool pred,bool polarity)
{
  CALL("Theory::tryGetInterpretedLaTeXName");

   //cout << "Get LaTeX for " << func << endl;

  // Used if no recorded template is found
  Interpretation i;

  if(pred){
    if(polarity){
      if(_predLaTeXnamesPos.find(func)){ return _predLaTeXnamesPos.get(func); }
      else if(_predLaTeXnamesNeg.find(func)){ 
        // If a negative record is found but no positive we negate it
        return "\neg ("+_predLaTeXnamesNeg.get(func)+")";
      }
    }
    else{ 
      if(_predLaTeXnamesNeg.find(func)){ return _predLaTeXnamesNeg.get(func); }
      else if(_predLaTeXnamesPos.find(func)){ 
        // If a positive record is found but no negative we negate it
        return "\neg ("+_predLaTeXnamesPos.get(func)+")";
      }
    }
    // We get here if no record is found for a predicate
    if(!isInterpretedPredicate(func)) return "";
    i = interpretPredicate(func);
  }
  else{
    if(_funcLaTeXnames.find(func)){ return _funcLaTeXnames.get(func); }
    // We get here if no record is found for a function
    if(!isInterpretedFunction(func)) return "";
    i = interpretFunction(func);
  }

  // There are some default templates
  // For predicates these include the notion of polarity
  vstring pol = polarity ? "" : " \\not ";

  //TODO do we want special symbols for quotient, remainder, floor, ceiling, truncate, round?

  switch(i){
  case EQUAL:return "a0 "+pol+"= a1";

  case INT_SUCCESSOR: return "a0++"; 
  case INT_UNARY_MINUS:
  case RAT_UNARY_MINUS:
  case REAL_UNARY_MINUS: return "-a0";

  case INT_GREATER: return "a0 "+pol+"> a1";
  case INT_GREATER_EQUAL: return "a0 "+pol+"\\geq a1";
  case INT_LESS: return "a0 "+pol+"< a1";
  case INT_LESS_EQUAL: return "a0 "+pol+"\\leq a1";
  case INT_DIVIDES: return "a0 "+pol+"\\| a1"; // check?

  case RAT_GREATER: return "a0 "+pol+"> a1";
  case RAT_GREATER_EQUAL: return "a0 "+pol+"\\geq a1";
  case RAT_LESS: return "a0 "+pol+"< a1";
  case RAT_LESS_EQUAL: return "a0 "+pol+"\\leq a1";

  case REAL_GREATER: return "a0 "+pol+"> a1"; 
  case REAL_GREATER_EQUAL: return "a0 "+pol+"\\geq a1";
  case REAL_LESS: return "a0 "+pol+"< a1";
  case REAL_LESS_EQUAL: return "a0 "+pol+"\\leq a1";

  case INT_PLUS: return "a0 + a1";
  case INT_MINUS: return "a0 - a1";
  case INT_MULTIPLY: return "a0 \\cdot a1";

  case RAT_PLUS: return "a0 + a1";
  case RAT_MINUS: return "a0 - a1";
  case RAT_MULTIPLY: return "a0 \\cdot a1";
  case RAT_QUOTIENT: return "a0 / a1";

  case REAL_PLUS: return "a0 + a1";
  case REAL_MINUS: return "a0 - a1";
  case REAL_MULTIPLY: return "a0 \\cdot a1";
  case REAL_QUOTIENT: return "a0 / a1";

  default: return "";
  } 

  return "";

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
