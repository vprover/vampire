
/*
 * File Theory.hpp.
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
 * @file Theory.hpp
 * Defines class Theory.
 */

#ifndef __Theory__
#define __Theory__

#include <math.h>

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Exception.hpp"

#include "Shell/TermAlgebra.hpp"

#include "Sorts.hpp"
#include "Term.hpp"

namespace Kernel {

/**
 * Exception to be thrown when the requested operation cannot be performed,
 * e.g. because of overflow of a native type.
 */
class ArithmeticException : public ThrowableBase {};

class IntegerConstantType
{
public:
  static unsigned getSort() { return Sorts::SRT_INTEGER; }

  typedef int InnerType;

  IntegerConstantType() {}
  IntegerConstantType(InnerType v) : _val(v) {}
  explicit IntegerConstantType(const vstring& str);

  IntegerConstantType operator+(const IntegerConstantType& num) const;
  IntegerConstantType operator-(const IntegerConstantType& num) const;
  IntegerConstantType operator-() const;
  IntegerConstantType operator*(const IntegerConstantType& num) const;
  IntegerConstantType operator/(const IntegerConstantType& num) const;
  IntegerConstantType operator%(const IntegerConstantType& num) const;

  // true if this divides num
  bool divides(const IntegerConstantType& num) const {
    CALL("IntegerConstantType:divides");
    // if this is zero it shouldn't divide anything, if num is zero dividing it doesn't make sense
    if(_val==0 || num._val==0){ return false; }
    // if this is bigger than num then the result cannot be an integer
    if(_val > num._val){ return false; }
    // now we only need to check the absolute value
    int safeVal=_val;
    if (_val < 0 && ! Lib::Int::safeUnaryMinus<int>(_val,safeVal)) {
      return false;
    }
    return (num._val % safeVal ==0);
  }

  float realDivide(const IntegerConstantType& num) const { 
    if(num._val==0) throw ArithmeticException();
    return ((float)_val)/num._val; 
  }
  int intDivide(const IntegerConstantType& num) const {
      CALL("IntegerConstantType::intDivide");
      ASS(num.divides(*this));
      if(num._val==0){ throw ArithmeticException(); }
      return _val/num._val;
  }
  // TODO: shouldn't we always be using intDivide for quotientE - when are they different (apart from real rounding)?
  IntegerConstantType quotientE(const IntegerConstantType& num) const { 
    CALL("IntegerConstantType::quotientE");
    //cout << "quotientE " << _val << " and " << num._val << endl;
    if(num.divides(*this)){
      return IntegerConstantType(intDivide(num));
    }
    if(num._val>0) return IntegerConstantType(::floor(realDivide(num)));
    else return IntegerConstantType(::ceil(realDivide(num)));
  }
  IntegerConstantType quotientT(const IntegerConstantType& num) const { 
    if(num.divides(*this)){
      return IntegerConstantType(intDivide(num));
    }
    return IntegerConstantType(::trunc(realDivide(num)));
  }
  IntegerConstantType quotientF(const IntegerConstantType& num) const { 
    if(num.divides(*this)){
      return IntegerConstantType(intDivide(num));
    }
    return IntegerConstantType(::floor(realDivide(num)));
  }

  bool operator==(const IntegerConstantType& num) const;
  bool operator>(const IntegerConstantType& num) const;

  bool operator!=(const IntegerConstantType& num) const { return !((*this)==num); }
  bool operator<(const IntegerConstantType& o) const { return o>(*this); }
  bool operator>=(const IntegerConstantType& o) const { return !(o>(*this)); }
  bool operator<=(const IntegerConstantType& o) const { return !((*this)>o); }

  InnerType toInner() const { return _val; }

  bool isZero(){ return _val==0; }
  bool isNegative(){ return _val<0; }

  static IntegerConstantType floor(RationalConstantType rat);
  static IntegerConstantType ceiling(RationalConstantType rat);

  static Comparison comparePrecedence(IntegerConstantType n1, IntegerConstantType n2);

  vstring toString() const;
private:
  InnerType _val;
};

inline
std::ostream& operator<< (ostream& out, const IntegerConstantType& val) {
  return out << val.toInner();
}

/**
 * A class for representing rational numbers
 *
 * The class uses IntegerConstantType to store the numerator and denominator.
 * This ensures that if there is an overflow in the operations, an exception
 * will be raised by the IntegerConstantType methods.
 */
struct RationalConstantType {
  typedef IntegerConstantType InnerType;

  static unsigned getSort() { return Sorts::SRT_RATIONAL; }

  RationalConstantType() {}

  RationalConstantType(InnerType num, InnerType den);
  RationalConstantType(const vstring& num, const vstring& den);
  RationalConstantType(InnerType num); //assuming den=1

  RationalConstantType operator+(const RationalConstantType& num) const;
  RationalConstantType operator-(const RationalConstantType& num) const;
  RationalConstantType operator-() const;
  RationalConstantType operator*(const RationalConstantType& num) const;
  RationalConstantType operator/(const RationalConstantType& num) const;

  RationalConstantType floor() const { 
    return RationalConstantType(IntegerConstantType::floor(*this));
  }
  RationalConstantType ceiling() const { 
    return RationalConstantType(IntegerConstantType::ceiling(*this));
  }
  RationalConstantType truncate() const { 
    return RationalConstantType(_num.quotientT(_den));
  }

  bool isInt() const;

  bool operator==(const RationalConstantType& num) const;
  bool operator>(const RationalConstantType& num) const;

  bool operator!=(const RationalConstantType& num) const { return !((*this)==num); }
  bool operator<(const RationalConstantType& o) const { return o>(*this); }
  bool operator>=(const RationalConstantType& o) const { return !(o>(*this)); }
  bool operator<=(const RationalConstantType& o) const { return !((*this)>o); }

  bool isZero(){ return _num.toInner()==0; } 
  // relies on the fact that cannonize ensures that _den>=0
  bool isNegative(){ ASS(_den>=0); return _num.toInner() < 0; }

  RationalConstantType quotientE(const RationalConstantType& num) const {
    if(_num.toInner()>0 && _den.toInner()>0){
       return ((*this)/num).floor(); 
    }
    else return ((*this)/num).ceiling();
  }
  RationalConstantType quotientT(const RationalConstantType& num) const {
    return ((*this)/num).truncate();
  }
  RationalConstantType quotientF(const RationalConstantType& num) const {
    return ((*this)/num).floor(); 
  }


  vstring toString() const;

  const InnerType& numerator() const { return _num; }
  const InnerType& denominator() const { return _den; }

  static Comparison comparePrecedence(RationalConstantType n1, RationalConstantType n2);

protected:
  void init(InnerType num, InnerType den);

private:
  void cannonize();

  InnerType _num;
  InnerType _den;
};

inline
std::ostream& operator<< (ostream& out, const RationalConstantType& val) {
  return out << val.toString();
}


class RealConstantType : public RationalConstantType
{
public:
  static unsigned getSort() { return Sorts::SRT_REAL; }

  RealConstantType() {}
  explicit RealConstantType(const vstring& number);
  explicit RealConstantType(const RationalConstantType& rat) : RationalConstantType(rat) {}

  RealConstantType operator+(const RealConstantType& num) const
  { return RealConstantType(RationalConstantType::operator+(num)); }
  RealConstantType operator-(const RealConstantType& num) const
  { return RealConstantType(RationalConstantType::operator-(num)); }
  RealConstantType operator-() const
  { return RealConstantType(RationalConstantType::operator-()); }
  RealConstantType operator*(const RealConstantType& num) const
  { return RealConstantType(RationalConstantType::operator*(num)); }
  RealConstantType operator/(const RealConstantType& num) const
  { return RealConstantType(RationalConstantType::operator/(num)); }

  RealConstantType floor() const { return RealConstantType(RationalConstantType::floor()); }
  RealConstantType truncate() const { return RealConstantType(RationalConstantType::truncate()); }
  RealConstantType ceiling() const { return RealConstantType(RationalConstantType::ceiling()); }

  RealConstantType quotientE(const RealConstantType& num) const
    { return RealConstantType(RationalConstantType::quotientE(num)); }
  RealConstantType quotientT(const RealConstantType& num) const
    { return RealConstantType(RationalConstantType::quotientT(num)); }
  RealConstantType quotientF(const RealConstantType& num) const
    { return RealConstantType(RationalConstantType::quotientF(num)); }

  vstring toNiceString() const;

  static Comparison comparePrecedence(RealConstantType n1, RealConstantType n2);
private:
  static bool parseDouble(const vstring& num, RationalConstantType& res);

};

inline
std::ostream& operator<< (ostream& out, const RealConstantType& val) {
  return out << val.toString();
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
    ARRAY_CONST,
    ARRAY_MERGE,

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
    CALL("inpretationFromIndexedInterpretation");

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

  static vstring getInterpretationName(Interpretation i);
  static unsigned getArity(Interpretation i);
  static bool isFunction(Interpretation i);
  static bool isInequality(Interpretation i);
  static OperatorType* getNonpolymorphicOperatorType(Interpretation i);

  static OperatorType* getArrayOperatorType(unsigned arraySort, Interpretation i);

  static bool hasSingleSort(Interpretation i);
  static unsigned getOperationSort(Interpretation i);
  static bool isConversionOperation(Interpretation i);
  static bool isLinearOperation(Interpretation i);
  static bool isNonLinearOperation(Interpretation i);
  static bool isPartialFunction(Interpretation i);

  static bool isPolymorphic(Interpretation i);

  unsigned getArrayExtSkolemFunction(unsigned i);

  static Theory theory_obj;
  static Theory* instance();

  void defineTupleTermAlgebra(unsigned arity, unsigned* sorts);

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
  /** Returns true if the argument is any interpreted predicate (including
      equality).
   */
  bool isInterpretedPredicate(Literal* lit);
  bool isInterpretedPredicate(Literal* lit, Interpretation itp);

  bool isInterpretedFunction(unsigned func);
  bool isInterpretedFunction(Term* t);
  bool isInterpretedFunction(TermList t);
  bool isInterpretedFunction(Term* t, Interpretation itp);
  bool isInterpretedFunction(TermList t, Interpretation itp);

  bool isInterpretedPartialFunction(unsigned func);
  bool isZero(TermList t);

  Interpretation interpretFunction(unsigned func);
  Interpretation interpretFunction(Term* t);
  Interpretation interpretFunction(TermList t);
  Interpretation interpretPredicate(unsigned pred);
  Interpretation interpretPredicate(Literal* t);

  void registerLaTeXPredName(unsigned func, bool polarity, vstring temp);
  void registerLaTeXFuncName(unsigned func, vstring temp);
  vstring tryGetInterpretedLaTeXName(unsigned func, bool pred,bool polarity=true);

private:
  // For recording the templates for predicate and function symbols
  DHMap<unsigned,vstring> _predLaTeXnamesPos;
  DHMap<unsigned,vstring> _predLaTeXnamesNeg;
  DHMap<unsigned,vstring> _funcLaTeXnames;

public:

  /**
   * Try to interpret the term list as an integer constant. If it is an
   * integer constant, return true and save the constant in @c res, otherwise
   * return false.
   */
  bool tryInterpretConstant(TermList trm, IntegerConstantType& res)
  {
    CALL("Theory::tryInterpretConstant(TermList,IntegerConstantType)");
    if (!trm.isTerm()) {
      return false;
    }
    return tryInterpretConstant(trm.term(),res);
  }
  bool tryInterpretConstant(const Term* t, IntegerConstantType& res);
  /**
   * Try to interpret the term list as an rational constant. If it is an
   * rational constant, return true and save the constant in @c res, otherwise
   * return false.
   */
  bool tryInterpretConstant(TermList trm, RationalConstantType& res)
  {
    CALL("Theory::tryInterpretConstant(TermList,RationalConstantType)");
    if (!trm.isTerm()) {
      return false;
    }
    return tryInterpretConstant(trm.term(),res);
  }
  bool tryInterpretConstant(const Term* t, RationalConstantType& res);
  /**
   * Try to interpret the term list as an real constant. If it is an
   * real constant, return true and save the constant in @c res, otherwise
   * return false.
   */
  bool tryInterpretConstant(TermList trm, RealConstantType& res)
  {
    CALL("Theory::tryInterpretConstant(TermList,RealConstantType)");
    if (!trm.isTerm()) {
      return false;
    }
    return tryInterpretConstant(trm.term(),res);
  }
  bool tryInterpretConstant(const Term* t, RealConstantType& res);

  Term* representConstant(const IntegerConstantType& num);
  Term* representConstant(const RationalConstantType& num);
  Term* representConstant(const RealConstantType& num);

  Term* representIntegerConstant(vstring str);
  Term* representRealConstant(vstring str);
private:
  Theory();
  static OperatorType* getConversionOperationType(Interpretation i);

  DHMap<unsigned,unsigned> _arraySkolemFunctions;

public:
  class Tuples {
  public:
    bool isFunctor(unsigned functor);
    unsigned getFunctor(unsigned arity, unsigned sorts[]);
    unsigned getFunctor(unsigned tupleSort);
    unsigned getProjectionFunctor(unsigned proj, unsigned tupleSort);
    bool findProjection(unsigned projFunctor, bool isPredicate, unsigned &proj);
  };

  static Theory::Tuples tuples_obj;
  static Theory::Tuples* tuples();
};

typedef Theory::Interpretation Interpretation;

/**
 * Pointer to the singleton Theory instance
 */
extern Theory* theory;

}

#endif // __Theory__
