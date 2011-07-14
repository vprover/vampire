/**
 * @file Theory.hpp
 * Defines class Theory.
 */

#ifndef __Theory__
#define __Theory__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Exception.hpp"

#include "Term.hpp"

namespace Kernel {

/**
 * Exception to be thrown when the requested operation cannot be performed,
 * e.g. because of overflow of a native type.
 */
class ArithmeticException : public ThrowableBase {};

#if 1

class IntegerConstantType
{
public:
  typedef int InnerType;

  IntegerConstantType() {}
  IntegerConstantType(InnerType v) : _val(v) {}
  explicit IntegerConstantType(const string& str);

  IntegerConstantType operator+(const IntegerConstantType& num) const;
  IntegerConstantType operator-(const IntegerConstantType& num) const;
  IntegerConstantType operator-() const;
  IntegerConstantType operator*(const IntegerConstantType& num) const;
  IntegerConstantType operator/(const IntegerConstantType& num) const;
  IntegerConstantType operator%(const IntegerConstantType& num) const;

  bool operator==(const IntegerConstantType& num) const;
  bool operator>(const IntegerConstantType& num) const;

  bool operator!=(const IntegerConstantType& num) const { return !((*this)==num); }
  bool operator<(const IntegerConstantType& o) const { return o>(*this); }
  bool operator>=(const IntegerConstantType& o) const { return !(o>(*this)); }
  bool operator<=(const IntegerConstantType& o) const { return !((*this)>o); }

  int toInt() const { return _val; }

  string toString() const;
private:
  InnerType _val;
};

#else

//these constant types are just a quick solution, there will be proper ones with
//overloaded operators, overflow checking/arbitrary precision etc...
typedef int IntegerConstantType;

#endif

/**
 * A class for representing rational numbers
 *
 * The class uses IntegerConstantType to store the numerator and denominator.
 * This ensures that if there is an overflow in the operations, an exception
 * will be raised by the IntegerConstantType methods.
 */
struct RationalConstantType {
  typedef IntegerConstantType InnerType;

  RationalConstantType() {}

  RationalConstantType(InnerType num, InnerType den);
  RationalConstantType(const string& num, const string& den);

  RationalConstantType operator+(const RationalConstantType& num) const;
  RationalConstantType operator-(const RationalConstantType& num) const;
  RationalConstantType operator-() const;
  RationalConstantType operator*(const RationalConstantType& num) const;
  RationalConstantType operator/(const RationalConstantType& num) const;

  bool operator==(const RationalConstantType& num) const;
  bool operator>(const RationalConstantType& num) const;

  bool operator!=(const RationalConstantType& num) const { return !((*this)==num); }
  bool operator<(const RationalConstantType& o) const { return o>(*this); }
  bool operator>=(const RationalConstantType& o) const { return !(o>(*this)); }
  bool operator<=(const RationalConstantType& o) const { return !((*this)>o); }


  string toString() const;

protected:
  void init(InnerType num, InnerType den);

private:
  void cannonize();

  InnerType _num;
  InnerType _den;
};

class RealConstantType : public RationalConstantType
{
public:
  RealConstantType() {}

  RealConstantType(const string& number);

};

//typedef double RealConstantType;

/** Obsolete */
typedef int InterpretedType;

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

    INT_GREATER,
    INT_GREATER_EQUAL,
    INT_LESS,
    INT_LESS_EQUAL,
    INT_DIVIDES,

    RAT_GREATER,
    RAT_GREATER_EQUAL,
    RAT_LESS,
    RAT_LESS_EQUAL,
    RAT_DIVIDES,

    REAL_GREATER,
    REAL_GREATER_EQUAL,
    REAL_LESS,
    REAL_LESS_EQUAL,
    REAL_DIVIDES,


    //functions

    INT_SUCCESSOR,
    INT_UNARY_MINUS,
    INT_PLUS,
    INT_MINUS,
    INT_MULTIPLY,
    INT_DIVIDE,
    INT_MODULO,

    RAT_UNARY_MINUS,
    RAT_PLUS,
    RAT_MINUS,
    RAT_MULTIPLY,
    RAT_DIVIDE,

    REAL_UNARY_MINUS,
    REAL_PLUS,
    REAL_MINUS,
    REAL_MULTIPLY,
    REAL_DIVIDE,

    //these are deprecated, left just so that the code compiles before references to them are removed
    GREATER,
    GREATER_EQUAL,
    LESS,
    LESS_EQUAL,
    SUCCESSOR,
    UNARY_MINUS,
    PLUS,
    MINUS,
    MULTIPLY,
    DIVIDE,
  };
  /**
   * Number of elements in the enum Interpretation
   *
   * At some points we make use of the fact that we can iterate through all
   * interpretations by going through the set {0,...,interpretationElementCount-1}.
   */
  static const unsigned interpretationElementCount=16;

  static unsigned getArity(Interpretation i);
  static bool isFunction(Interpretation i);
  static bool isInequality(Interpretation i);
  static BaseType* getOperationType(Interpretation i);
  static unsigned getOperationSort(Interpretation i);


  static Theory* instance();

  bool isInterpretedConstant(Term* t);
  bool isInterpretedConstant(TermList t);
  bool isInterpretedPredicate(Literal* lit);
  bool isInterpretedPredicate(Literal* lit, Interpretation itp);
  bool isInterpretedFunction(Term* t);
  bool isInterpretedFunction(TermList t);
  bool isInterpretedFunction(Term* t, Interpretation itp);
  bool isInterpretedFunction(TermList t, Interpretation itp);

  Interpretation interpretFunction(Term* t);
  Interpretation interpretFunction(TermList t);
  Interpretation interpretPredicate(Literal* t);

  InterpretedType interpretConstant(Term* t);
  InterpretedType interpretConstant(TermList t);
  unsigned getFnNum(Interpretation itp);
  unsigned getPredNum(Interpretation itp);

  Term* getRepresentation(InterpretedType val);
  Term* fun1(Interpretation itp, TermList arg);
  Term* fun2(Interpretation itp, TermList arg1, TermList arg2);

  Literal* pred2(Interpretation itp, bool polarity, TermList arg1, TermList arg2);

  TermList zero();
  TermList one();
  TermList minusOne();

private:
  Theory();

  Term* _zero;
  Term* _one;
  Term* _minusOne;
  DHMap<InterpretedType, Term*> _constants;

};

typedef Theory::Interpretation Interpretation;

/**
 * Pointer to the singleton Theory instance
 */
extern Theory* theory;

}

#endif // __Theory__
