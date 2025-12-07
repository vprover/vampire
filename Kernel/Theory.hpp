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
 * @file Theory.hpp
 * Defines class Theory.
 */

#ifndef __Theory__
#define __Theory__

#include <cstdint>

#include "Forwards.hpp"
#include "OperatorType.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Reflection.hpp"

#include "Term.hpp"

#include "mini-gmp.h"
#include "mini-mpq.h"

namespace Kernel {

class IntegerConstantType;
struct RationalConstantType;
class RealConstantType;

template<class T>
struct QR { T quot; T rem; };

#define MK_CAST_OP(Type, OP, ToCast)                                                      \
  friend auto operator OP(Type l, ToCast const& r) { return l OP Type(r); }               \
  friend auto operator OP(ToCast const& l, Type r) { return Type(l) OP r; }               \

#define MK_CAST_OPS(Type, ToCast)                                                         \
  MK_CAST_OP(Type, *, ToCast)                                                             \
  MK_CAST_OP(Type, +, ToCast)                                                             \
  MK_CAST_OP(Type, -, ToCast)                                                             \
  MK_CAST_OP(Type, <, ToCast)                                                             \
  MK_CAST_OP(Type, >, ToCast)                                                             \
  MK_CAST_OP(Type, <=,ToCast)                                                             \
  MK_CAST_OP(Type, >=,ToCast)                                                             \
  MK_CAST_OP(Type, ==,ToCast)                                                             \
  MK_CAST_OP(Type, !=,ToCast)                                                             \

#define MK_SIGN_OPS                                                                       \
  Sign sign()       const;                                                                \
  bool isZero()     const { return sign() == Sign::Zero; }                                \
  bool isNegative() const { return sign() == Sign::Neg;  }                                \
  bool isPositive() const { return sign() == Sign::Pos;  }                                \


class DivByZeroException : public Exception 
{ 
public:
  DivByZeroException() : Exception("divided by zero"){} 
};

enum class Sign : std::uint8_t {
  Zero = 0,
  Pos = 1,
  Neg = 2,
};

inline std::ostream& operator<<(std::ostream& out, Sign const& self)
{
  switch(self) {
    case Sign::Zero: return out << "0";
    case Sign::Pos: return out << "+";
    case Sign::Neg: return out << "-";
  }
  ASSERTION_VIOLATION
}

template<class T> struct MpzToMachineInt;

template<> struct MpzToMachineInt<long> {
  using Int = long;
  static bool fits(mpz_t const self) { return mpz_fits_sint_p(self);  }
  static Int cvt(mpz_t const self) { return mpz_get_si(self);  }
};
#define CONV_FROM_NUM_LIMITS(Long) \
  static Option<Int> _cvt(mpz_t const self) {  \
    if (!MpzToMachineInt<Long>::fits(self)) \
      return {}; \
    auto v = MpzToMachineInt<Long>::cvt(self); \
    auto lim = std::numeric_limits<Int>{}; \
    if (lim.min() <= v && v <= lim.max()) { \
      return some(Int(v)); \
    } else { \
      return {}; \
    } \
  } \
  static bool fits(mpz_t const self) { return _cvt(self).isSome(); } \
  static Int cvt(mpz_t const self) { return _cvt(self).unwrap(); } \

template<> struct MpzToMachineInt<unsigned long> {
  using Int = unsigned long;

  static Int truncate(mpz_t const self) { return mpz_get_ui(self); }
  static bool fits(mpz_t const self) { return mpz_sgn(self) >= 0 && mpz_fits_uint_p(self);  }
  static Int cvt(mpz_t const self) { return mpz_get_ui(self);  }
};

template<> struct MpzToMachineInt<int> {
  using Int = int;
  CONV_FROM_NUM_LIMITS(long)
};

template<> struct MpzToMachineInt<unsigned> {
  using Int = unsigned;
  CONV_FROM_NUM_LIMITS(unsigned long)
  static Int truncate(mpz_t const self) { return mpz_get_ui(self); }
};



class IntegerConstantType
{
  mpz_t _val;
public:
  static TermList getSort() { return AtomicSort::intSort(); }

  IntegerConstantType() { mpz_init(_val); }
  explicit IntegerConstantType(int v) : IntegerConstantType() { mpz_set_si(_val, v); }

  IntegerConstantType(IntegerConstantType     && o) : IntegerConstantType() { mpz_swap(_val, o._val); }
  IntegerConstantType(IntegerConstantType const& o) : IntegerConstantType() {  mpz_set(_val, o._val); }
  IntegerConstantType& operator=(IntegerConstantType     && o) { mpz_swap(_val, o._val); return *this; }
  IntegerConstantType& operator=(IntegerConstantType const& o) {  mpz_set(_val, o._val); return *this; }

  ~IntegerConstantType() { mpz_clear(_val); }

  IntegerConstantType operator+(const IntegerConstantType& num) const;
  IntegerConstantType operator-(const IntegerConstantType& num) const;
  IntegerConstantType operator^(unsigned long num) const;

  static Option<IntegerConstantType> parse(std::string const&);

  IntegerConstantType operator-() const;
  IntegerConstantType operator*(const IntegerConstantType& num) const;
  IntegerConstantType& operator++() { mpz_add_ui(_val,_val,1); return *this; }
  IntegerConstantType& operator--() { mpz_sub_ui(_val,_val,1); return *this; }
  IntegerConstantType operator++(int) { auto out = IntegerConstantType(*this); mpz_add_ui(_val,_val, 1); return out; }
  IntegerConstantType operator--(int) { auto out = IntegerConstantType(*this); mpz_sub_ui(_val,_val, 1); return out; }

  IntegerConstantType& operator*=(IntegerConstantType const& r) { mpz_mul(_val, _val, r._val); return *this; }
  IntegerConstantType& operator+=(IntegerConstantType const& r) { mpz_add(_val, _val, r._val); return *this; }
  IntegerConstantType& operator-=(IntegerConstantType const& r) { mpz_sub(_val, _val, r._val); return *this; }

  // true if this divides num
  bool divides(const IntegerConstantType& num) const;
  IntegerConstantType inverseModulo(IntegerConstantType const& modulus) const;
  IntegerConstantType intDivide(const IntegerConstantType& num) const;

  using QR = Kernel::QR<IntegerConstantType>;

#define MK_QR(X)                                                                          \
  QR div ## X(int i) const;                                                               \
  QR div ## X(const IntegerConstantType& num) const;                                      \
  template<class T>                                                                       \
  IntegerConstantType remainder ## X(T const& num) const { return div ## X(num).rem;  }   \
  template<class T>                                                                       \
  IntegerConstantType  quotient ## X(T const& num) const { return div ## X(num).quot; }   \

  MK_QR(E)
  MK_QR(T)
  MK_QR(F)

  IntegerConstantType gcd(IntegerConstantType const& rhs) const;
  IntegerConstantType lcm(IntegerConstantType const& rhs) const;

  Comparison compare(IntegerConstantType const& num) const { return Comparison(mpz_cmp(_val, num._val)); }
  IMPL_COMPARISONS_FROM_COMPARE(IntegerConstantType);
  IMPL_EQ_FROM_COMPARE(IntegerConstantType);

  template<class T> 
  bool fits() const { return MpzToMachineInt<T>::fits(_val); }

  template<class T> 
  Option<T> cvt() const { return someIf(MpzToMachineInt<T>::fits(_val), [&]() { return MpzToMachineInt<T>::cvt(_val); }); }

  template<class T> 
  T truncate() const { return MpzToMachineInt<T>::truncate(_val); }

  void rshiftBits(mp_bitcnt_t cnt) { mpz_tdiv_q_2exp(_val, _val, cnt); }

  MK_SIGN_OPS

  IntegerConstantType abs() const;
  IntegerConstantType log2() const;

  static Comparison comparePrecedence(IntegerConstantType n1, IntegerConstantType n2);
  size_t hash() const;
  auto defaultHash () const { return DefaultHash ::hash(truncate<unsigned long>()); }
  auto defaultHash2() const { return DefaultHash2::hash(truncate<unsigned long>()); }

  friend std::ostream& operator<<(std::ostream& out, const IntegerConstantType& val);
  friend struct RationalConstantType;
  friend void init_mpq(mpq_t out, RationalConstantType const&);
private:
  MK_CAST_OPS(IntegerConstantType, int)
};

/**
 * A class for representing rational numbers
 *
 * The class uses IntegerConstantType to store the numerator and denominator.
 * This ensures that if there is an overflow in the operations, an exception
 * will be raised by the IntegerConstantType methods.
 */
struct RationalConstantType {
  typedef IntegerConstantType InnerType;
  friend void init_mpq(mpq_t out, RationalConstantType const&);

  static TermList getSort() { return AtomicSort::rationalSort(); }



  RationalConstantType() {}

  explicit RationalConstantType(int n);
  explicit RationalConstantType(IntegerConstantType num);
  RationalConstantType(int num, int den);
  RationalConstantType(IntegerConstantType num, IntegerConstantType den);

  static Option<RationalConstantType> parse(std::string const& number)
  {
    size_t i = number.find_first_of("/");
    if (i == std::string::npos) {
      return IntegerConstantType::parse(number)
        .map([](auto x) { return RationalConstantType(std::move(x)); });
    } else {
      return IntegerConstantType::parse(number.substr(0,i))
        .map([&](auto a) {
            return IntegerConstantType::parse(number.substr(i + 1))
               .map([&](auto b) {
                   return RationalConstantType(std::move(a),std::move(b));
               });
            }).flatten();
    }
  }

  RationalConstantType operator+(const RationalConstantType& num) const;
  RationalConstantType operator-(const RationalConstantType& num) const;
  RationalConstantType operator-() const;
  RationalConstantType operator*(const RationalConstantType& num) const;
  RationalConstantType operator/(const RationalConstantType& num) const;

  RationalConstantType& operator*=(RationalConstantType const& r) { _num *= r._num; _den *= r._den;  cannonize(); return *this; }
  RationalConstantType& operator+=(RationalConstantType const& r) { *this = *this + r; return *this; }
  RationalConstantType& operator-=(RationalConstantType const& r) { *this = *this - r; return *this; }
  RationalConstantType& operator/=(RationalConstantType const& r) { _num *= r._den; _den *= r._num;  cannonize(); return *this; }

  RationalConstantType inverse() const { return RationalConstantType(1) / *this; }
  IntegerConstantType floor() const;
  IntegerConstantType ceiling() const;
  IntegerConstantType truncate() const { return _num.quotientT(_den); }

  bool isInt() const;

  bool operator==(const RationalConstantType& num) const;
  bool operator>(const RationalConstantType& num) const;

  bool operator!=(const RationalConstantType& num) const { return !((*this)==num); }
  bool operator<(const RationalConstantType& o) const { return o>(*this); }
  bool operator>=(const RationalConstantType& o) const { return !(o>(*this)); }
  bool operator<=(const RationalConstantType& o) const { return !((*this)>o); }

  RationalConstantType abs() const;

  const InnerType& numerator() const { return _num; }
  const InnerType& denominator() const { return _den; }
  size_t hash() const;

  MK_SIGN_OPS

  static Comparison comparePrecedence(RationalConstantType n1, RationalConstantType n2);

  friend std::ostream& operator<<(std::ostream& out, const RationalConstantType& val); 

  MK_CAST_OPS(RationalConstantType, int)
  MK_CAST_OPS(RationalConstantType, IntegerConstantType)
  MK_CAST_OP(RationalConstantType, /, int)

  auto defaultHash () const { return HashUtils::combine(_num.defaultHash(), _den.defaultHash()); }
  auto defaultHash2() const { return HashUtils::combine(_num.defaultHash2(), _den.defaultHash2()); }

private:
  void cannonize();

  InnerType _num;
  InnerType _den;
};

std::ostream& operator<<(std::ostream& out, const IntegerConstantType& val); 


class RealConstantType : public RationalConstantType
{
public:
  static TermList getSort() { return AtomicSort::realSort(); }

  RealConstantType() {}
  RealConstantType(RealConstantType&&) = default;
  RealConstantType(const RealConstantType&) = default;
  RealConstantType& operator=(const RealConstantType&) = default;

  static Option<RealConstantType> parse(std::string const&);
  explicit RealConstantType(const RationalConstantType& rat) : RationalConstantType(rat) {}
  RealConstantType(IntegerConstantType num) : RationalConstantType(num) {}
  RealConstantType(int num, int den) : RationalConstantType(num, den) {}
  explicit RealConstantType(int number) : RealConstantType(RationalConstantType(number)) {}
  RealConstantType(typename RationalConstantType::InnerType  num, typename RationalConstantType::InnerType den) : RealConstantType(RationalConstantType(num, den)) {}


#define BIN_OP_FROM_RAT(op) \
  RealConstantType operator op(const RealConstantType& num) const \
  { return RealConstantType(RationalConstantType::operator op(num)); } \

  BIN_OP_FROM_RAT(+)
  BIN_OP_FROM_RAT(-)
  BIN_OP_FROM_RAT(*)
  BIN_OP_FROM_RAT(/)

  RealConstantType operator-() const
  { return RealConstantType(RationalConstantType::operator-()); }

  IntegerConstantType floor() const { return this->RationalConstantType::floor(); }
  IntegerConstantType ceiling() const { return this->RationalConstantType::ceiling(); }
  IntegerConstantType truncate() const { return this->RationalConstantType::truncate(); }

  MK_SIGN_OPS

  RealConstantType abs() const;

  size_t hash() const;
  static Comparison comparePrecedence(RealConstantType n1, RealConstantType n2);

  /* currently we only represent rational numerals */ 
  bool isRat() const { return true;  }

  RealConstantType inverse() const { return RealConstantType(1) / *this; }

  friend std::ostream& operator<<(std::ostream& out, const RealConstantType& val);
  MK_CAST_OPS(RealConstantType, int)
  MK_CAST_OPS(RealConstantType, IntegerConstantType)
  MK_CAST_OP(RealConstantType, /, int)

};

inline bool operator<(const RealConstantType& lhs ,const RealConstantType& rhs) { 
  return static_cast<const RationalConstantType&>(lhs) < static_cast<const RationalConstantType&>(rhs);
}
inline bool operator>(const RealConstantType& lhs, const RealConstantType& rhs) {
  return static_cast<const RationalConstantType&>(lhs) > static_cast<const RationalConstantType&>(rhs);
}
inline bool operator<=(const RealConstantType& lhs, const RealConstantType& rhs) {
  return static_cast<const RationalConstantType&>(lhs) <= static_cast<const RationalConstantType&>(rhs);
}
inline bool operator>=(const RealConstantType& lhs, const RealConstantType& rhs) {
  return static_cast<const RationalConstantType&>(lhs) >= static_cast<const RationalConstantType&>(rhs);
}

/**
 * A singleton class handling tasks related to theory symbols in Vampire
 */
class Theory
{
public:
  /**
   * Interpreted symbols and predicates
   *
   * If interpreted_evaluation is enabled, predicates GREATER_EQUAL,
   * LESS and LESS_EQUAL should not appear in the run of the
   * SaturationAlgorithm (they'll be immediately simplified by the
   * InterpretedEvaluation simplification).
   */
  enum Interpretation
  {
    //predicates
    EQUAL,

    INT_IS_INT,
    INT_IS_RAT,
    INT_IS_REAL,
    INT_GREATER,
    INT_GREATER_EQUAL,
    INT_LESS,
    INT_LESS_EQUAL,
    INT_DIVIDES,

    RAT_IS_INT,
    RAT_IS_RAT,
    RAT_IS_REAL,
    RAT_GREATER,
    RAT_GREATER_EQUAL,
    RAT_LESS,
    RAT_LESS_EQUAL,

    REAL_IS_INT,
    REAL_IS_RAT,
    REAL_IS_REAL,
    REAL_GREATER,
    REAL_GREATER_EQUAL,
    REAL_LESS,
    REAL_LESS_EQUAL,

    //numeric functions

    INT_SUCCESSOR,
    INT_UNARY_MINUS,
    INT_PLUS,  // sum in TPTP
    INT_MINUS, // difference in TPTP
    INT_MULTIPLY,
    INT_QUOTIENT_E,
    INT_QUOTIENT_T,
    INT_QUOTIENT_F,
    INT_REMAINDER_E,
    INT_REMAINDER_T,
    INT_REMAINDER_F,
    INT_FLOOR,
    INT_CEILING,
    INT_TRUNCATE,
    INT_ROUND,
    INT_ABS,

    RAT_UNARY_MINUS,
    RAT_PLUS, // sum in TPTP
    RAT_MINUS,// difference in TPTP
    RAT_MULTIPLY,
    RAT_QUOTIENT,
    RAT_QUOTIENT_E,
    RAT_QUOTIENT_T,
    RAT_QUOTIENT_F,
    RAT_REMAINDER_E,
    RAT_REMAINDER_T,
    RAT_REMAINDER_F,
    RAT_FLOOR,
    RAT_CEILING,
    RAT_TRUNCATE,
    RAT_ROUND,

    REAL_UNARY_MINUS,
    REAL_PLUS,  // plus in TPTP
    REAL_MINUS, // difference in TPTP
    REAL_MULTIPLY,
    REAL_QUOTIENT,
    REAL_QUOTIENT_E,
    REAL_QUOTIENT_T,
    REAL_QUOTIENT_F,
    REAL_REMAINDER_E,
    REAL_REMAINDER_T,
    REAL_REMAINDER_F,
    REAL_FLOOR,
    REAL_CEILING,
    REAL_TRUNCATE,
    REAL_ROUND,

    //conversion functions
    INT_TO_INT,
    INT_TO_RAT,
    INT_TO_REAL,
    RAT_TO_INT,
    RAT_TO_RAT,
    RAT_TO_REAL,
    REAL_TO_INT,
    REAL_TO_RAT,
    REAL_TO_REAL,

    // array functions
    ARRAY_SELECT,
    ARRAY_BOOL_SELECT,
    ARRAY_STORE,

    INVALID_INTERPRETATION // LEAVE THIS AS THE LAST ELEMENT OF THE ENUM
  };

  enum IndexedInterpretation {
    FOR_NOW_EMPTY
  };

  typedef std::pair<IndexedInterpretation, unsigned> ConcreteIndexedInterpretation;

  /**
   * Interpretations represent the abstract concept of an interpreted operation vampire knows about.
   *
   * Some of them are polymorphic, such the ones for ARRAYs, and only become a concrete operation when supplied with OperatorType*.
   * To identify these, MonomorphisedInterpretation (see below) can be used. However, notice that the appropriate Symbol always carries
   * an Interpretation (if interpreted) and an OperatorType*.
   *
   * Other operations might be, in fact, indexed families of operations, and need an additional index (unsigned) to be specified.
   * To keep the Symbol structure from growing for their sake, these IndexedInterpretations are instantiated to a concrete member of a family on demand
   * and we keep track of this instantiation in _indexedInterpretations (see below). Members of _indexedInterpretations
   * implicitly "inhabit" a range of values in Interpretation after INVALID_INTERPRETATION, so that again an
   * Interpretation (this time >= INVALID_INTERPRETATION) and an OperatorType* are enough to identify a member of an indexed family.
   */

  typedef std::pair<Interpretation, OperatorType*> MonomorphisedInterpretation;

private:
  DHMap<ConcreteIndexedInterpretation,Interpretation> _indexedInterpretations;

public:

  static unsigned numberOfFixedInterpretations() {
    return INVALID_INTERPRETATION;
  }

  Interpretation interpretationFromIndexedInterpretation(IndexedInterpretation ii, unsigned index)
  {
    ConcreteIndexedInterpretation cii = std::make_pair(ii,index);

    Interpretation res;
    if (!_indexedInterpretations.find(cii, res)) {
      res = static_cast<Interpretation>(numberOfFixedInterpretations() + _indexedInterpretations.size());
      _indexedInterpretations.insert(cii, res);
    }
    return res;
  }

  static bool isPlus(Interpretation i){
    return i == INT_PLUS || i == RAT_PLUS || i == REAL_PLUS;
  }

  static std::string getInterpretationName(Interpretation i);
  static unsigned getArity(Interpretation i);
  static bool isFunction(Interpretation i);
  static bool isInequality(Interpretation i);
  static OperatorType* getNonpolymorphicOperatorType(Interpretation i);

  static OperatorType* getArrayOperatorType(TermList arraySort, Interpretation i);

  static bool hasSingleSort(Interpretation i);
  static TermList getOperationSort(Interpretation i);
  static bool isConversionOperation(Interpretation i);
  static bool isLinearOperation(Interpretation i);
  static bool isNonLinearOperation(Interpretation i);
  bool isPartiallyInterpretedFunction(Term* t);
  bool partiallyDefinedFunctionUndefinedForArgs(Term* t);
  // static bool isPartialFunction(Interpretation i);

  static bool isPolymorphic(Interpretation i);

  unsigned getArrayExtSkolemFunction(TermList sort);

  static Theory theory_obj;
  static Theory* instance();

  Shell::TermAlgebra* getTupleTermAlgebra(unsigned arity);

  /** Returns true if the argument is an interpreted constant
   */
  bool isInterpretedConstant(unsigned func);
  bool isInterpretedConstant(Term* t);
  bool isInterpretedConstant(TermList t);
  /** Returns true if the argument is an interpreted number
   */
  bool isInterpretedNumber(Term* t);
  bool isInterpretedNumber(TermList t);

  /** Returns false if pred is equality.  Returns true if the argument is any
      other interpreted predicate.
   */
  bool isInterpretedPredicate(unsigned pred);
    
  bool isInterpretedEquality(Literal* lit);
  bool isInterpretedPredicate(Literal* lit, Interpretation itp);
  bool isInterpretedPredicate(unsigned pred, Interpretation itp);
  bool isInterpretedPredicate(Literal* lit);

  bool isInterpretedFunction(unsigned func);
  bool isInterpretedFunction(Term* t);
  bool isInterpretedFunction(TermList t);
  bool isInterpretedFunction(unsigned func, Interpretation itp);
  bool isInterpretedFunction(Term* t, Interpretation itp);
  bool isInterpretedFunction(TermList t, Interpretation itp);

  // bool isInterpretedPartialFunction(unsigned func);
  bool isZero(TermList t);

  Interpretation interpretFunction(unsigned func);
  Interpretation interpretFunction(Term* t);
  Interpretation interpretFunction(TermList t);
  Interpretation interpretPredicate(unsigned pred);
  Interpretation interpretPredicate(Literal* t);

public:

  /**
   * Try to interpret the term list as an integer constant. If it is an
   * integer constant, return true and save the constant in @c res, otherwise
   * return false.
   */
  bool tryInterpretConstant(TermList trm, IntegerConstantType& res)
  {
    if (!trm.isTerm()) {
      return false;
    }
    return tryInterpretConstant(trm.term(),res);
  }
  bool tryInterpretConstant(const Term* t, IntegerConstantType& res);
  bool tryInterpretConstant(unsigned functor, IntegerConstantType& res);


  Option<IntegerConstantType> tryInterpretConstant(unsigned functor);
  /**
   * Try to interpret the term list as an rational constant. If it is an
   * rational constant, return true and save the constant in @c res, otherwise
   * return false.
   */
  bool tryInterpretConstant(TermList trm, RationalConstantType& res);
  bool tryInterpretConstant(const Term* t, RationalConstantType& res);
  bool tryInterpretConstant(unsigned functor, RationalConstantType& res);
  /**
   * Try to interpret the term list as an real constant. If it is an
   * real constant, return true and save the constant in @c res, otherwise
   * return false.
   */
  bool tryInterpretConstant(TermList trm, RealConstantType& res)
  {
    if (!trm.isTerm()) {
      return false;
    }
    return tryInterpretConstant(trm.term(),res);
  }
  bool tryInterpretConstant(const Term* t, RealConstantType& res);
  bool tryInterpretConstant(unsigned functor, RealConstantType& res);

  Term* representConstant(const IntegerConstantType& num);
  Term* representConstant(const RationalConstantType& num);
  Term* representConstant(const RealConstantType& num);

private:
  Theory();
  static OperatorType* getConversionOperationType(Interpretation i);

  DHMap<TermList,unsigned> _arraySkolemFunctions;

public:
  class Tuples {
  public:
    bool isConstructor(Term* t);
    unsigned getConstructor(unsigned arity);
    unsigned getProjectionFunctor(unsigned arity, unsigned proj);
    bool findProjection(unsigned projFunctor, bool isPredicate, unsigned &proj);
  };

  static Theory::Tuples tuples_obj;
  static Theory::Tuples* tuples();
};

#define ANY_INTERPRETED_PREDICATE                                                         \
         Kernel::Theory::EQUAL:                                                           \
    case Kernel::Theory::INT_IS_INT:                                                      \
    case Kernel::Theory::INT_IS_RAT:                                                      \
    case Kernel::Theory::INT_IS_REAL:                                                     \
    case Kernel::Theory::INT_GREATER:                                                     \
    case Kernel::Theory::INT_GREATER_EQUAL:                                               \
    case Kernel::Theory::INT_LESS:                                                        \
    case Kernel::Theory::INT_LESS_EQUAL:                                                  \
    case Kernel::Theory::INT_DIVIDES:                                                     \
    case Kernel::Theory::RAT_IS_INT:                                                      \
    case Kernel::Theory::RAT_IS_RAT:                                                      \
    case Kernel::Theory::RAT_IS_REAL:                                                     \
    case Kernel::Theory::RAT_GREATER:                                                     \
    case Kernel::Theory::RAT_GREATER_EQUAL:                                               \
    case Kernel::Theory::RAT_LESS:                                                        \
    case Kernel::Theory::RAT_LESS_EQUAL:                                                  \
    case Kernel::Theory::REAL_IS_INT:                                                     \
    case Kernel::Theory::REAL_IS_RAT:                                                     \
    case Kernel::Theory::REAL_IS_REAL:                                                    \
    case Kernel::Theory::REAL_GREATER:                                                    \
    case Kernel::Theory::REAL_GREATER_EQUAL:                                              \
    case Kernel::Theory::REAL_LESS:                                                       \
    case Kernel::Theory::ARRAY_BOOL_SELECT:                                               \
    case Kernel::Theory::REAL_LESS_EQUAL

#define ANY_INTERPRETED_FUNCTION                                                          \
         Kernel::Theory::INT_SUCCESSOR:                                                   \
    case Kernel::Theory::INT_UNARY_MINUS:                                                 \
    case Kernel::Theory::INT_PLUS:                                                        \
    case Kernel::Theory::INT_MINUS:                                                       \
    case Kernel::Theory::INT_MULTIPLY:                                                    \
    case Kernel::Theory::INT_QUOTIENT_E:                                                  \
    case Kernel::Theory::INT_QUOTIENT_T:                                                  \
    case Kernel::Theory::INT_QUOTIENT_F:                                                  \
    case Kernel::Theory::INT_REMAINDER_E:                                                 \
    case Kernel::Theory::INT_REMAINDER_T:                                                 \
    case Kernel::Theory::INT_REMAINDER_F:                                                 \
    case Kernel::Theory::INT_FLOOR:                                                       \
    case Kernel::Theory::INT_CEILING:                                                     \
    case Kernel::Theory::INT_TRUNCATE:                                                    \
    case Kernel::Theory::INT_ROUND:                                                       \
    case Kernel::Theory::INT_ABS:                                                         \
    case Kernel::Theory::RAT_UNARY_MINUS:                                                 \
    case Kernel::Theory::RAT_PLUS:                                                        \
    case Kernel::Theory::RAT_MINUS:                                                       \
    case Kernel::Theory::RAT_MULTIPLY:                                                    \
    case Kernel::Theory::RAT_QUOTIENT:                                                    \
    case Kernel::Theory::RAT_QUOTIENT_E:                                                  \
    case Kernel::Theory::RAT_QUOTIENT_T:                                                  \
    case Kernel::Theory::RAT_QUOTIENT_F:                                                  \
    case Kernel::Theory::RAT_REMAINDER_E:                                                 \
    case Kernel::Theory::RAT_REMAINDER_T:                                                 \
    case Kernel::Theory::RAT_REMAINDER_F:                                                 \
    case Kernel::Theory::RAT_FLOOR:                                                       \
    case Kernel::Theory::RAT_CEILING:                                                     \
    case Kernel::Theory::RAT_TRUNCATE:                                                    \
    case Kernel::Theory::RAT_ROUND:                                                       \
    case Kernel::Theory::REAL_UNARY_MINUS:                                                \
    case Kernel::Theory::REAL_PLUS:                                                       \
    case Kernel::Theory::REAL_MINUS:                                                      \
    case Kernel::Theory::REAL_MULTIPLY:                                                   \
    case Kernel::Theory::REAL_QUOTIENT:                                                   \
    case Kernel::Theory::REAL_QUOTIENT_E:                                                 \
    case Kernel::Theory::REAL_QUOTIENT_T:                                                 \
    case Kernel::Theory::REAL_QUOTIENT_F:                                                 \
    case Kernel::Theory::REAL_REMAINDER_E:                                                \
    case Kernel::Theory::REAL_REMAINDER_T:                                                \
    case Kernel::Theory::REAL_REMAINDER_F:                                                \
    case Kernel::Theory::REAL_FLOOR:                                                      \
    case Kernel::Theory::REAL_CEILING:                                                    \
    case Kernel::Theory::REAL_TRUNCATE:                                                   \
    case Kernel::Theory::REAL_ROUND:                                                      \
    case Kernel::Theory::INT_TO_INT:                                                      \
    case Kernel::Theory::INT_TO_RAT:                                                      \
    case Kernel::Theory::INT_TO_REAL:                                                     \
    case Kernel::Theory::RAT_TO_INT:                                                      \
    case Kernel::Theory::RAT_TO_RAT:                                                      \
    case Kernel::Theory::RAT_TO_REAL:                                                     \
    case Kernel::Theory::REAL_TO_INT:                                                     \
    case Kernel::Theory::REAL_TO_RAT:                                                     \
    case Kernel::Theory::REAL_TO_REAL:                                                    \
    case Kernel::Theory::ARRAY_SELECT:                                                    \
    case Kernel::Theory::ARRAY_STORE

typedef Theory::Interpretation Interpretation;

/**
 * Pointer to the singleton Theory instance
 */
extern Theory* theory;

std::ostream& operator<<(std::ostream& out, Kernel::Theory::Interpretation const& self);

} // namespace Kernel

template<>
struct std::hash<Kernel::IntegerConstantType>
{
  size_t operator()(Kernel::IntegerConstantType const& self) const noexcept 
  { return self.hash(); }
};

template<>
struct std::hash<Kernel::RationalConstantType>
{
  size_t operator()(Kernel::RationalConstantType const& self) const noexcept 
  { return self.hash(); }
};


template<>
struct std::hash<Kernel::RealConstantType>
{
  size_t operator()(Kernel::RealConstantType const& self) const noexcept 
  { return self.hash(); }
};


#endif // __Theory__
