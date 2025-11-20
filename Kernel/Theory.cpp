/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Theory.hpp"
#include "Debug/Assertion.hpp"

#include <cmath>

#include "Debug/Assertion.hpp"

#include "Kernel/TermIterators.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Shell/Skolem.hpp"

#include "Signature.hpp"
#include "SortHelper.hpp"
#include "OperatorType.hpp"
#include "Term.hpp"
#include "Kernel/NumTraits.hpp"
#include <cstdio>
#include <iostream>

#  pragma GCC diagnostic push
#    pragma GCC diagnostic ignored "-Wsign-compare"
#    include "mini-gmp.c"
#    include "mini-mpq.c"
#  pragma GCC diagnostic pop

std::string to_string(mpz_t const& self) {
  auto s = mpz_sizeinbase(self, /* base */ 10);
  auto str = new char[s + 2];
  mpz_get_str(str, /* base */ 10, self);
  auto out = std::string(str);
  delete[] str;
  return out;
}

std::ostream& output(std::ostream& out, mpz_t const& self)
{ return out << to_string(self); }

using namespace Lib;

namespace Kernel {

Option<IntegerConstantType> IntegerConstantType::parse(std::string const& str)
{
  auto out = IntegerConstantType(0);
  if (-1 == mpz_set_str(out._val, str.c_str(), /* base */ 10)) {
    return {};
  } else {
    return some(out);
  }
}

#define IMPL_BIN_OP(fun, mpz_fun)                                                         \
  IntegerConstantType IntegerConstantType::fun(const IntegerConstantType& num) const      \
  { auto out = IntegerConstantType(0); mpz_fun(out._val, this->_val, num._val); return out; } \

  // TODO move semantics
IMPL_BIN_OP(operator+, mpz_add)
IMPL_BIN_OP(operator-, mpz_sub)
IMPL_BIN_OP(operator*, mpz_mul)
IMPL_BIN_OP(lcm, mpz_lcm)
IMPL_BIN_OP(gcd, mpz_gcd)
IMPL_BIN_OP(inverseModulo, mpz_invert)

#undef IMPL_BIN_OP

IntegerConstantType IntegerConstantType::operator^(unsigned long num) const
{ 
  auto out = IntegerConstantType(0); 
  mpz_pow_ui(out._val, this->_val, num); 
  return out; 
}

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

IntegerConstantType IntegerConstantType::intDivide(const IntegerConstantType& num) const 
{
  ASS_REP(num.divides(*this),  Output::cat(num, " does not divide ", *this) );
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
      throw DivByZeroException();
    case Sign::Pos:
      mpz_fdiv_qr(out.quot._val, out.rem._val, n._val, d._val);
      break;
    case Sign::Neg:
      mpz_cdiv_qr(out.quot._val, out.rem._val, n._val, d._val);
      break;
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

///////////////////////
// RationalConstantType
//

RationalConstantType::RationalConstantType(InnerType num, InnerType den)
  : _num(num), _den(den)
{ cannonize(); }

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

Option<RationalConstantType> parseRat(const std::string& num)
{
  std::string newNum;
  IntegerConstantType denominator = IntegerConstantType(1);
  bool haveDecimal = false;
  bool neg = false;
  size_t nlen = num.size();
  for(size_t i=0; i<nlen; i++) {
    if (num[i]=='.') {
      if (haveDecimal) {
        return {};
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
      return {};
    }
  }
  if (neg) {
    newNum = '-'+newNum;
  }
  auto numerator = IntegerConstantType::parse(newNum).unwrap();
  return some(RationalConstantType(numerator, denominator));
}

Option<RationalConstantType> parseExponentInteger(std::string const& number, const char* exponentChars) {
  auto i = number.find_first_of(exponentChars);
  if (i != std::string::npos) {
    auto base = parseRat(number.substr(0, i));
    int exp = 0;
    if (Int::stringToInt(number.substr(i + 1).c_str(), exp) && base.isSome()) {
      return some(
          exp >= 0 ? (*base) * (IntegerConstantType(10) ^ (unsigned long)exp)
                   : (*base) / RationalConstantType((IntegerConstantType(10) ^ (unsigned long)abs(exp))));
    }
  }
  return {};
}

Option<RealConstantType> RealConstantType::parse(std::string const& number)
{
  if (auto r = parseExponentInteger(number, "E")) {
    return some(RealConstantType(std::move(*r)));
  } else if (auto r = parseExponentInteger(number, "e")) {
    return some(RealConstantType(std::move(*r)));
  } else if (auto r = parseRat(number))  {
    return some(RealConstantType(std::move(*r)));
  } else {
    return {};
  }
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


using namespace std;
using namespace Lib;

namespace Kernel {


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

unsigned Theory::Tuples::getConstructor(unsigned arity)
{
  return theory->getTupleTermAlgebra(arity)->constructor(0)->functor();
}

bool Theory::Tuples::isConstructor(Term* t)
{
  return !t->isSpecial() && !t->isSort() && getConstructor(t->numTypeArguments()) == t->functor();
}

unsigned Theory::Tuples::getProjectionFunctor(unsigned arity, unsigned proj)
{
  auto c = theory->getTupleTermAlgebra(arity)->constructor(0);

  ASS_L(proj, c->arity());

  return c->destructorFunctor(proj);
}

// TODO: replace with a constant time algorithm
bool Theory::Tuples::findProjection(unsigned projFunctor, bool isPredicate, unsigned &proj) {
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
 * This function creates a type for conversion function @c i.
 *
 * @c i must be a type conversion operation.
 */
OperatorType* Theory::getConversionOperationType(Interpretation i)
{
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

std::string Theory::getInterpretationName(Interpretation interp) {
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

TermAlgebra* Theory::getTupleTermAlgebra(unsigned arity)
{
  auto tupleTypeCon = env.signature->getTupleConstructor(arity);
  auto typeVars = TermStack::fromIterator(varRange(0, arity));

  auto tupleSort = AtomicSort::tupleSort(arity, typeVars.begin());

  if (env.signature->isTermAlgebraSort(tupleSort)) {
    return env.signature->getTermAlgebraOfSort(tupleSort);
  }

  auto args = typeVars;
  args.loadFromIterator(varRange(arity, 2*arity));

  auto functor = env.signature->addFreshFunction(2*arity, "tuple");
  auto tupleType = OperatorType::getFunctionType(arity, args.begin(), tupleSort, arity);
  env.signature->getFunction(functor)->setType(tupleType);
  env.signature->getFunction(functor)->markTermAlgebraCons();

  Array<unsigned> destructors(arity);
  for (unsigned i = 0; i < arity; i++) {
    auto destructor = env.signature->addFreshFunction(arity+1, "proj");
    auto destSym = env.signature->getFunction(destructor);
    destSym->setType(OperatorType::getFunctionType({ tupleSort }, typeVars[i], arity));
    destSym->markTermAlgebraDest();
    destructors[i] = destructor;
  }

  auto constructor = new Shell::TermAlgebraConstructor(functor, destructors);

  Shell::TermAlgebraConstructor* constructors[] = { constructor };
  auto res = new Shell::TermAlgebra(tupleSort, 1, constructors, false);
  env.signature->addTermAlgebra(res);
  return res;
}

bool Theory::isInterpretedConstant(unsigned func)
{
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
  if (t->isSpecial()) { return false; }

  return t->numTermArguments()==0 && env.signature->getFunction(t->functor())->interpreted();
}

/**
 * Return true iff @b t is an interpreted constant
 */
bool Theory::isInterpretedConstant(TermList t)
{
  return t.isTerm() && isInterpretedConstant(t.term());
}

/**
 * Return true iff @b t is a constant with a numerical interpretation
 */
bool Theory::isInterpretedNumber(Term* t)
{
  return isInterpretedConstant(t) && env.signature->getFunction(t->functor())->interpretedNumber();
}

/**
 * Return true iff @b t is a constant with a numerical interpretation
 */
bool Theory::isInterpretedNumber(TermList t)
{
  return isInterpretedConstant(t) && env.signature->getFunction(t.term()->functor())->interpretedNumber();
}

/**
 * Return true iff @b pred is an interpreted predicate
 */
bool Theory::isInterpretedPredicate(unsigned pred)
{ return env.signature->getPredicate(pred)->interpreted(); }

/**
 * Return true iff @b lit has an interpreted predicate
 */
bool Theory::isInterpretedEquality(Literal* lit)
{
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
  return env.signature->getPredicate(lit->functor())->interpreted();
}


bool Theory::isInterpretedPredicate(unsigned pred, Interpretation itp)
{ return isInterpretedPredicate(pred) && interpretPredicate(pred) == itp; }

/**
 * Return true iff @b lit has an interpreted predicate interpreted
 * as @b itp
 */
bool Theory::isInterpretedPredicate(Literal* lit, Interpretation itp)
{
  return isInterpretedPredicate(lit) && interpretPredicate(lit)==itp;
}

bool Theory::isInterpretedFunction(unsigned func)
{
  if (func>=Term::SPECIAL_FUNCTOR_LOWER_BOUND) {
    return false;
  }

  return env.signature->getFunction(func)->interpreted() && env.signature->functionArity(func)!=0;
}

bool Theory::isZero(TermList term)
{
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
  return isInterpretedFunction(t->functor());
}

/**
 * Return true iff @b t is an interpreted function
 */
bool Theory::isInterpretedFunction(TermList t)
{
  return t.isTerm() && isInterpretedFunction(t.term());
}

Interpretation Theory::interpretFunction(unsigned func)
{
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
  ASS(isInterpretedFunction(t));

  return interpretFunction(t->functor());
}

/**
 * Assuming @b t is an interpreted function, return its interpretation
 */
Interpretation Theory::interpretFunction(TermList t)
{
  ASS(t.isTerm());

  return interpretFunction(t.term());
}

Interpretation Theory::interpretPredicate(unsigned pred)
{
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
  if (t->numTermArguments() != 0 || t->isSpecial()) {
    return false;
  }
  unsigned func = t->functor();
  return tryInterpretConstant(func, res);
} // Theory::tryInterpretConstant


bool Theory::tryInterpretConstant(unsigned func, IntegerConstantType& res)
{
  Signature::Symbol* sym = env.signature->getFunction(func);
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
  if (t->numTermArguments() != 0 || t->isSpecial()) {
    return false;
  }
  unsigned func = t->functor();
  return tryInterpretConstant(func, res);
} // Theory::tryInterpretConstant 

bool Theory::tryInterpretConstant(unsigned func, RationalConstantType& res)
{
  Signature::Symbol* sym = env.signature->getFunction(func);
  if (!sym->rationalConstant()) {
    return false;
  }
  res = sym->rationalValue();
  return true;
}

bool Theory::tryInterpretConstant(TermList trm, RationalConstantType& res)
{
  if (!trm.isTerm()) {
    return false;
  }
  return tryInterpretConstant(trm.term(),res);
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
  if (t->numTermArguments() != 0 || t->isSpecial()) {
    return false;
  }
  unsigned func = t->functor();
  return tryInterpretConstant(func, res);
} // // Theory::tryInterpretConstant

bool Theory::tryInterpretConstant(unsigned func, RealConstantType& res)
{
  Signature::Symbol* sym = env.signature->getFunction(func);
  if (!sym->realConstant()) {
    return false;
  }
  res = sym->realValue();
  return true;
}

Term* Theory::representConstant(const IntegerConstantType& num)
{
  unsigned func = env.signature->addNumeralConstant(num);
  return Term::create(func, 0, 0);
}

Term* Theory::representConstant(const RationalConstantType& num)
{
  unsigned func = env.signature->addNumeralConstant(num);
  return Term::create(func, 0, 0);
}

Term* Theory::representConstant(const RealConstantType& num)
{
  unsigned func = env.signature->addNumeralConstant(num);
  return Term::create(func, 0, 0);
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

std::ostream& operator<<(std::ostream& out, IntegerConstantType const& self)
{ return output(out, self._val); }

std::ostream& operator<<(std::ostream& out, RationalConstantType const& self)
#if NICE_THEORY_OUTPUT
{ return self.isInt() ? out << self.numerator() 
                      : out << self.numerator() << "/" << self.denominator(); }
#else 
{ return out << self.numerator() << "/" << self.denominator(); }
#endif // NICE_THEORY_OUTPUT

std::ostream& operator<<(std::ostream& out, RealConstantType const& self)
{ return out << (RationalConstantType const&)self; }


/**
 * Return true iff @b t is an interpreted function interpreted
 * as @b itp
 */
bool Theory::isInterpretedFunction(unsigned f, Interpretation itp)
{
  return isInterpretedFunction(f) && interpretFunction(f)==itp;
}
/**
 * Return true iff @b t is an interpreted function interpreted
 * as @b itp
 */
bool Theory::isInterpretedFunction(Term* t, Interpretation itp)
{

  return isInterpretedFunction(t->functor(), itp);
}

/**
 * Return true iff @b t is an interpreted function interpreted
 * as @b itp
 */
bool Theory::isInterpretedFunction(TermList t, Interpretation itp)
{
  return t.isTerm() && isInterpretedFunction(t.term(), itp);
}

} // namespace Kernel
