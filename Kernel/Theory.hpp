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
  
  float realDivide(const IntegerConstantType& num) const { 
    if(num._val==0) throw ArithmeticException();
    return ((float)_val)/num._val; 
  }
  IntegerConstantType quotientE(const IntegerConstantType& num) const { 
    if(num._val>0) return IntegerConstantType(::floor(realDivide(num)));
    else return IntegerConstantType(::ceil(realDivide(num)));
  }
  IntegerConstantType quotientT(const IntegerConstantType& num) const { 
    return IntegerConstantType(::trunc(realDivide(num)));
  }
  IntegerConstantType quotientF(const IntegerConstantType& num) const { 
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
    INT_MODULO,
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
    REAL_TO_REAL

    // IMPORTANT - if you add something to end of this, update it in LastNonStructuredInterepretation 
    
    //INVALID_INTERPRETATION // replaced by LastNonStructuredInterepretation
  };

  unsigned LastNonStructuredInterepretation(){ return REAL_TO_REAL; }

    /**
     * Maximal element number in the enum Interpretation
     *
     * At some points we make use of the fact that we can iterate through all
     * interpretations by going through the set {0,...,MAX_INTERPRETED_ELEMENT}.
     */
  unsigned MaxInterpretedElement(){
    return LastNonStructuredInterepretation() + _structuredSortInterpretations.size(); 
  }

  unsigned numberOfInterpretations(){
    return LastNonStructuredInterepretation() + LastStructuredInterpretation();
  }

  bool isValidInterpretation(Interpretation i){
    return i <= MaxInterpretedElement();
  }

  bool isPlus(Interpretation i){
    return i == INT_PLUS || i == RAT_PLUS || i == REAL_PLUS;
  }

 /*
  * StructuredSortInterpretations begin from the last interpretation in Interpretation
  *
  * They will be initialised as MaxInterpretedElement()+1
  *
  */


  /** enum for the kinds of StructuredSort interpretations **/
  enum class StructuredSortInterpretation
  {
    ARRAY_SELECT,
    ARRAY_BOOL_SELECT,
    ARRAY_STORE,
    // currently unused
    LIST_HEAD,
    LIST_TAIL,
    LIST_CONS,
    LIST_IS_EMPTY
  };
  unsigned LastStructuredInterpretation(){
    return static_cast<unsigned>(StructuredSortInterpretation::LIST_IS_EMPTY);
  }
  unsigned getSymbolForStructuredSort(unsigned sort, StructuredSortInterpretation interp);
  Interpretation getInterpretation(unsigned sort, StructuredSortInterpretation i){
    auto key = make_pair(sort, i);
    unsigned interpretation;
    if (!_structuredSortInterpretations.find(key, interpretation)) {
      interpretation = MaxInterpretedElement() + 1;
      _structuredSortInterpretations.insert(key, interpretation);
    }
    return static_cast<Interpretation>(interpretation);
  }
  bool isStructuredSortInterpretation(Interpretation i){
    return i > LastNonStructuredInterepretation();
  }
  unsigned getSort(Interpretation i){
    return getData(i).first;
  }

  static vstring getInterpretationName(Interpretation i);
  static unsigned getArity(Interpretation i);
  static bool isFunction(Interpretation i);
  static bool isInequality(Interpretation i);
  static Sorts::StructuredSort getInterpretedSort(StructuredSortInterpretation ssi);
  static BaseType* getOperationType(Interpretation i);
  static BaseType* getStructuredSortOperationType(Interpretation i);
  static bool hasSingleSort(Interpretation i);
  static unsigned getOperationSort(Interpretation i);
  static bool isConversionOperation(Interpretation i);
  static bool isLinearOperation(Interpretation i);
  static bool isNonLinearOperation(Interpretation i);

  static bool isArrayOperation(Interpretation i);
  static unsigned getArrayOperationSort(Interpretation i);
  static unsigned getArrayDomainSort(Interpretation i);

  unsigned getArrayExtSkolemFunction(unsigned i);
    
  static Theory theory_obj;
  static Theory* instance();

  void defineTupleTermAlgebra(unsigned arity, unsigned* sorts);

  bool isInterpretedConstant(unsigned func);
  bool isInterpretedConstant(Term* t);
  bool isInterpretedConstant(TermList t);
  bool isInterpretedNumber(TermList t);

  bool isInterpretedPredicate(unsigned pred);
  bool isInterpretedPredicate(Literal* lit);
  bool isInterpretedPredicate(Literal* lit, Interpretation itp);

  bool isInterpretedFunction(unsigned func);
  bool isInterpretedFunction(Term* t);
  bool isInterpretedFunction(TermList t);
  bool isInterpretedFunction(Term* t, Interpretation itp);
  bool isInterpretedFunction(TermList t, Interpretation itp);

  Interpretation interpretFunction(unsigned func);
  Interpretation interpretFunction(Term* t);
  Interpretation interpretFunction(TermList t);
  Interpretation interpretPredicate(unsigned pred);
  Interpretation interpretPredicate(Literal* t);

  unsigned getFnNum(Interpretation itp);
  unsigned getPredNum(Interpretation itp);

  void registerLaTeXPredName(unsigned func, bool polarity, vstring temp);
  void registerLaTeXFuncName(unsigned func, vstring temp);
  vstring tryGetInterpretedLaTeXName(unsigned func, bool pred,bool polarity=true);
  
private:
  // For recording the templates for predicate and function symbols
  DHMap<unsigned,vstring> _predLaTeXnamesPos;
  DHMap<unsigned,vstring> _predLaTeXnamesNeg;
  DHMap<unsigned,vstring> _funcLaTeXnames;

public:

  Term* fun1(Interpretation itp, TermList arg);
  Term* fun2(Interpretation itp, TermList arg1, TermList arg2);
  Term* fun3(Interpretation itp, TermList arg1, TermList arg2, TermList arg3);
  Literal* pred2(Interpretation itp, bool polarity, TermList arg1, TermList arg2);

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
  static FunctionType* getConversionOperationType(Interpretation i);

  DHMap<unsigned,unsigned> _arraySkolemFunctions;

public:
  unsigned getStructuredOperationSort(Interpretation i){
    return getData(i).first;
  }
  StructuredSortInterpretation convertToStructured(Interpretation i){
    return getData(i).second;
  }
private:    
  pair<unsigned,StructuredSortInterpretation> getData(Interpretation i){
    ASS(isStructuredSortInterpretation(i));
    auto it = _structuredSortInterpretations.items();
    while(it.hasNext()){
      auto entry = it.next();
      if(entry.second==i) return entry.first;
    }
    ASSERTION_VIOLATION;
  }

  DHMap<pair<unsigned,StructuredSortInterpretation>,unsigned> _structuredSortInterpretations;

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
