/**
 * @file Theory.cpp
 * Implements class Theory.
 */

#include <math.h>

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Signature.hpp"

#include "Theory.hpp"

namespace Kernel
{

using namespace Lib;

///////////////////////
// IntegerConstantType
//

IntegerConstantType::IntegerConstantType(const string& str)
{
  CALL("IntegerConstantType::IntegerConstantType(string)");

  if(!Int::stringToInt(str, _val)) {
    //TODO: raise exception only on overflow, the proper syntax should be guarded by assertion
    throw ArithmeticException();
  }
}

IntegerConstantType IntegerConstantType::operator+(const IntegerConstantType& num) const
{
  CALL("IntegerConstantType::operator+");

  InnerType res;
  if(!Int::safePlus(_val, num._val, res)) {
    throw ArithmeticException();
  }
  return IntegerConstantType(res);
}

IntegerConstantType IntegerConstantType::operator-(const IntegerConstantType& num) const
{
  CALL("IntegerConstantType::operator-/1");

  InnerType res;
  if(!Int::safeMinus(_val, num._val, res)) {
    throw ArithmeticException();
  }
  return IntegerConstantType(res);
}

IntegerConstantType IntegerConstantType::operator-() const
{
  CALL("IntegerConstantType::operator-/0");

  InnerType res;
  if(!Int::safeUnaryMinus(_val, res)) {
    throw ArithmeticException();
  }
  return IntegerConstantType(res);
}

IntegerConstantType IntegerConstantType::operator*(const IntegerConstantType& num) const
{
  CALL("IntegerConstantType::operator*");

  InnerType res;
  if(!Int::safeMultiply(_val, num._val, res)) {
    throw ArithmeticException();
  }
  return IntegerConstantType(res);
}

IntegerConstantType IntegerConstantType::operator/(const IntegerConstantType& num) const
{
  CALL("IntegerConstantType::operator/");

  //TODO: check if division corresponds to the TPTP semantic
  if(num._val==0) {
    throw ArithmeticException();
  }
  return IntegerConstantType(_val/num._val);
}

IntegerConstantType IntegerConstantType::operator%(const IntegerConstantType& num) const
{
  CALL("IntegerConstantType::operator%");

  //TODO: check if modulo corresponds to the TPTP semantic
  if(num._val==0) {
    throw ArithmeticException();
  }
  return IntegerConstantType(_val%num._val);
}

bool IntegerConstantType::operator==(const IntegerConstantType& num) const
{
  CALL("IntegerConstantType::operator==");

  return _val==num._val;
}

bool IntegerConstantType::operator>(const IntegerConstantType& num) const
{
  CALL("IntegerConstantType::operator>");

  return _val>num._val;
}

IntegerConstantType IntegerConstantType::floor(RationalConstantType rat)
{
  CALL("IntegerConstantType::floor");

  IntegerConstantType numer = rat.numerator();
  IntegerConstantType denom = rat.denominator();
  ASS_REP(denom>0, denom.toString());

  if(numer>0) {
    return numer/denom;
  }

  IntegerConstantType numerAbs = (numer>=0) ? numer : -numer;
  IntegerConstantType absRes = numerAbs/denom;
  if(numer%denom!=0) {
    absRes = absRes+1;
  }
  return -absRes;
}

Comparison IntegerConstantType::comparePrecedence(IntegerConstantType n1, IntegerConstantType n2)
{
  CALL("IntegerConstantType::comparePrecedence");
  try {
    bool invert = false;
    Comparison res;
    if(n1<0 && n2>=0) {
      swap(n1, n2);
      invert = true;
    }

    if(n1>=0) {
      if(n2>=0) {
	return Int::compare(n1.toInt(), n2.toInt());
      }
      else {
	//we invert numbers to become negative, because this prevents overflows
	IntegerConstantType negN1 = -n1;
	if(negN1==n2) {
	  res = LESS;
	}
	else {
	  res = Int::compare(n2.toInt(), negN1.toInt());
	}
      }
    }
    else {
      ASS(n2<0);
      invert = !invert;
      res = Int::compare(n2.toInt(), n1.toInt());
    }

    if(invert) { res = static_cast<Comparison>(-res); }
    return res;
  }
  catch(ArithmeticException) {
    ASSERTION_VIOLATION;
    throw;
  }
}

string IntegerConstantType::toString() const
{
  CALL("IntegerConstantType::toString");

  return Int::toString(_val);
}

///////////////////////
// RationalConstantType
//

RationalConstantType::RationalConstantType(InnerType num, InnerType den)
{
  CALL("RationalConstantType::RationalConstantType");

  init(num, den);
}

RationalConstantType::RationalConstantType(const string& num, const string& den)
{
  CALL("RationalConstantType::RationalConstantType");

  init(InnerType(num), InnerType(den));
}

void RationalConstantType::init(InnerType num, InnerType den)
{
  CALL("RationalConstantType::init");

  _num = num;
  _den = den;
  cannonize();
}

RationalConstantType RationalConstantType::operator+(const RationalConstantType& o) const
{
  CALL("RationalConstantType::operator+");

  if(_den==o._den) {
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
  CALL("RationalConstantType::operator/");

  return RationalConstantType(_num*o._den, _den*o._num);
}

bool RationalConstantType::isInt() const
{
  CALL("RationalConstantType::isInt");

  return _den==1;
}

bool RationalConstantType::operator==(const RationalConstantType& o) const
{
  CALL("IntegerConstantType::operator==");

  return _num==o._num && _den==o._den;
}

bool RationalConstantType::operator>(const RationalConstantType& o) const
{
  CALL("IntegerConstantType::operator>");

  return (_num*o._den)>(o._num*_den);
}


string RationalConstantType::toString() const
{
  CALL("RationalConstantType::toString");

  string numStr = _num.toString();
  string denStr = _den.toString();

//  return "("+numStr+"/"+denStr+")";
  return numStr+"/"+denStr;
}

/**
 * Ensure the GCD of numerator and denominator is 1, and the only
 * number that may be negative is numerator
 */
void RationalConstantType::cannonize()
{
  CALL("RationalConstantType::cannonize");

  int gcd = Int::gcd(_num.toInt(), _den.toInt());
  if(gcd!=1) {
    _num = _num/InnerType(gcd);
    _den = _den/InnerType(gcd);
  }
  if(_den<0) {
    _num = -_num;
    _den = -_den;
  }
}

Comparison RationalConstantType::comparePrecedence(RationalConstantType n1, RationalConstantType n2)
{
  CALL("RationalConstantType::comparePrecedence");
  try {

    if(n1==n2) { return EQUAL; }

    bool haveRepr1 = true;
    bool haveRepr2 = true;

    IntegerConstantType repr1, repr2;

    try {
      repr1 = n1.numerator()+n1.denominator();
    } catch(ArithmeticException) {
      haveRepr1 = false;
    }

    try {
      repr2 = n2.numerator()+n2.denominator();
    } catch(ArithmeticException) {
      haveRepr2 = false;
    }

    if(haveRepr1 && haveRepr2) {
      Comparison res = IntegerConstantType::comparePrecedence(repr1, repr2);
      if(res==EQUAL) {
	res = IntegerConstantType::comparePrecedence(n1.numerator(), n2.numerator());
      }
      ASS_NEQ(res, EQUAL);
      return res;
    }
    if(haveRepr1 && !haveRepr2) {
      return LESS;
    }
    if(!haveRepr1 && haveRepr2) {
      return GREATER;
    }

    ASS(!haveRepr1);
    ASS(!haveRepr2);

    Comparison res = IntegerConstantType::comparePrecedence(n1.denominator(), n2.denominator());
    if(res==EQUAL) {
      res = IntegerConstantType::comparePrecedence(n1.numerator(), n2.numerator());
    }
    ASS_NEQ(res, EQUAL);
    return res;
  }
  catch(ArithmeticException) {
    ASSERTION_VIOLATION;
    throw;
  }
}


///////////////////////
// RealConstantType
//

Comparison RealConstantType::comparePrecedence(RealConstantType n1, RealConstantType n2)
{
  CALL("RealConstantType::comparePrecedence");

  return RationalConstantType::comparePrecedence(n1, n2);
}

bool RealConstantType::parseDouble(const string& num, RationalConstantType& res)
{
  CALL("RealConstantType::parseDouble");

  try {
    string newNum;
    IntegerConstantType denominator = 1;
    bool haveDecimal = false;
    bool neg = false;
    size_t nlen = num.size();
    for(size_t i=0; i<nlen; i++) {
      if(num[i]=='.') {
	if(haveDecimal) {
	  return false;
	}
	haveDecimal = true;
      }
      else if(i==0 && num[i]=='-') {
	neg = true;
      }
      else if(num[i]>='0' && num[i]<='9') {
	if(newNum=="0") {
	  newNum = num[i];
	}
	else {
	  newNum += num[i];
	}
	if(haveDecimal) {
	  denominator = denominator * 10;
	}
      }
      else {
	return false;
      }
    }
    if(neg) {
      newNum = '-'+newNum;
    }
    IntegerConstantType numerator(newNum);
    res = RationalConstantType(numerator, denominator);
  } catch(ArithmeticException) {
    return false;
  }
  LOG("arith_num_parsing","Real parsing: \""<<num<<"\" --> "<<res.toString());
  return true;
}

RealConstantType::RealConstantType(const string& number)
{
  CALL("RealConstantType::RealConstantType");

  RationalConstantType value;
  if(parseDouble(number, value)) {
    init(value.numerator(), value.denominator());
    return;
  }

  double numDbl;
  if(!Int::stringToDouble(number, numDbl)) {
    //TODO: raise exception only on overflow, the proper syntax should be guarded by assertion
    throw ArithmeticException();
  }
  InnerType denominator = 1;
  while(floor(numDbl)!=numDbl) {
    denominator = denominator*10;
    numDbl *= 10;
    LOG("arith_num_parsing","multiplying double to get integer: "<<numDbl);
  }

  InnerType::InnerType numerator = static_cast<InnerType::InnerType>(numDbl);
  if(numerator!=numDbl) {
    //the numerator part of double doesn't fit inside the inner integer type
    throw ArithmeticException();
  }
  init(numerator, denominator);
}

string RealConstantType::toNiceString() const
{
  CALL("RealConstantType::toNiceString");

  if(denominator().toInt()==1) {
    return numerator().toString()+".0";
  }
  return toString();
}

/////////////////
// Theory
//

Theory* theory = Theory::instance();

/**
 * Accessor for the singleton instance of the Theory class.
 */
Theory* Theory::instance()
{
  static Theory* inst=new Theory;

  return inst;
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
  ASS_LE(i,MAX_INTERPRETED_ELEMENT);

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
  case RAT_DIVIDES:

  case REAL_GREATER:
  case REAL_GREATER_EQUAL:
  case REAL_LESS:
  case REAL_LESS_EQUAL:
  case REAL_DIVIDES:

  case INT_PLUS:
  case INT_MINUS:
  case INT_MULTIPLY:
  case INT_DIVIDE:
  case INT_MODULO:

  case RAT_PLUS:
  case RAT_MINUS:
  case RAT_MULTIPLY:
  case RAT_DIVIDE:

  case REAL_PLUS:
  case REAL_MINUS:
  case REAL_MULTIPLY:
  case REAL_DIVIDE:
    return 2;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Return true iff the symbol that is interpreted by Interpretation
 * is a function (false is returned for predicates)
 */
bool Theory::isFunction(Interpretation i)
{
  CALL("Signature::InterpretedSymbol::isFunction");
  ASS_LE(i,MAX_INTERPRETED_ELEMENT);

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
  case INT_DIVIDE:
  case INT_MODULO:

  case RAT_PLUS:
  case RAT_MINUS:
  case RAT_MULTIPLY:
  case RAT_DIVIDE:

  case REAL_PLUS:
  case REAL_MINUS:
  case REAL_MULTIPLY:
  case REAL_DIVIDE:
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
  case RAT_DIVIDES:

  case REAL_GREATER:
  case REAL_GREATER_EQUAL:
  case REAL_LESS:
  case REAL_LESS_EQUAL:
  case REAL_DIVIDES:

  case INT_IS_INT:
  case INT_IS_RAT:
  case INT_IS_REAL:
  case RAT_IS_INT:
  case RAT_IS_RAT:
  case RAT_IS_REAL:
  case REAL_IS_INT:
  case REAL_IS_RAT:
  case REAL_IS_REAL:
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
  ASS_LE(i,MAX_INTERPRETED_ELEMENT);

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
  case EQUAL:
  case INT_TO_RAT:
  case INT_TO_REAL:
  case RAT_TO_INT:
  case RAT_TO_REAL:
  case REAL_TO_INT:
  case REAL_TO_RAT:
    return false;
  default:
    return true;
  }
}

/**
 * This function can be called for operations for which  the
 * function @c hasSingleSort returns true
 */
unsigned Theory::getOperationSort(Interpretation i)
{
  CALL("Theory::getOperationSort");
  ASS(hasSingleSort(i));
  ASS_LE(i,MAX_INTERPRETED_ELEMENT);

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
  case INT_DIVIDE:
  case INT_MODULO:

  case INT_TO_INT:
  case INT_IS_INT:
  case INT_IS_RAT:
  case INT_IS_REAL:
    return Sorts::SRT_INTEGER;

  case RAT_UNARY_MINUS:
  case RAT_PLUS:
  case RAT_MINUS:
  case RAT_MULTIPLY:
  case RAT_DIVIDE:
  case RAT_GREATER:
  case RAT_GREATER_EQUAL:
  case RAT_LESS:
  case RAT_LESS_EQUAL:
  case RAT_DIVIDES:

  case RAT_TO_RAT:
  case RAT_IS_INT:
  case RAT_IS_RAT:
  case RAT_IS_REAL:
    return Sorts::SRT_RATIONAL;

  case REAL_UNARY_MINUS:
  case REAL_PLUS:
  case REAL_MINUS:
  case REAL_MULTIPLY:
  case REAL_DIVIDE:
  case REAL_GREATER:
  case REAL_GREATER_EQUAL:
  case REAL_LESS:
  case REAL_LESS_EQUAL:
  case REAL_DIVIDES:

  case REAL_TO_REAL:
  case REAL_IS_INT:
  case REAL_IS_RAT:
  case REAL_IS_REAL:
    return Sorts::SRT_REAL;

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

/**
 * This function creates a type for converion function @c i.
 *
 * @c i must be a type conversion operation.
 */
FunctionType* Theory::getConversionOperationType(Interpretation i)
{
  CALL("Theory::getConversionOperationType");

  unsigned from, to;
  switch(i) {
  case INT_TO_RAT:
    from = Sorts::SRT_INTEGER;
    to = Sorts::SRT_RATIONAL;
    break;
  case INT_TO_REAL:
    from = Sorts::SRT_INTEGER;
    to = Sorts::SRT_REAL;
    break;
  case RAT_TO_INT:
    from = Sorts::SRT_RATIONAL;
    to = Sorts::SRT_INTEGER;
    break;
  case RAT_TO_REAL:
    from = Sorts::SRT_RATIONAL;
    to = Sorts::SRT_REAL;
    break;
  case REAL_TO_INT:
    from = Sorts::SRT_REAL;
    to = Sorts::SRT_INTEGER;
    break;
  case REAL_TO_RAT:
    from = Sorts::SRT_REAL;
    to = Sorts::SRT_RATIONAL;
    break;
  default:
    ASSERTION_VIOLATION;
  }
  BaseType* res = BaseType::makeType(1, &from, to);
  ASS(res->isFunctionType());
  return static_cast<FunctionType*>(res);
}

/**
 * Return type of the function representing interpreted function/predicate @c i.
 */
BaseType* Theory::getOperationType(Interpretation i)
{
  CALL("Theory::getOperationType");
  ASS_NEQ(i, EQUAL);

  if(isConversionOperation(i)) {
    return getConversionOperationType(i);
  }
  ASS(hasSingleSort(i));

  unsigned sort = getOperationSort(i);
  unsigned arity = getArity(i);

  static DArray<unsigned> domainSorts;
  domainSorts.init(arity, sort);

  unsigned resSort = isFunction(i) ? sort : Sorts::SRT_BOOL;

  return BaseType::makeType(arity, domainSorts.array(), resSort);
}

bool Theory::isInterpretedConstant(unsigned func)
{
  CALL("Theory::isInterpretedConstant");

  if(func>=Term::SPECIAL_FUNCTOR_LOWER_BOUND) {
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

  if(t->isSpecial()) { return false; }

  return t->arity()==0 && env.signature->getFunction(t->functor())->interpreted();
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
bool Theory::isInterpretedPredicate(Literal* lit)
{
  CALL("Theory::isInterpretedPredicate");

  return isInterpretedPredicate(lit->functor());
}

/**
 * Return true iff @b lit has an interpreted predicate interpreted
 * as @b itp
 */
bool Theory::isInterpretedPredicate(Literal* lit, Interpretation itp)
{
  CALL("Theory::isInterpretedPredicate/2");

  return env.signature->getPredicate(lit->functor())->interpreted() &&
      interpretPredicate(lit)==itp;
}

bool Theory::isInterpretedFunction(unsigned func)
{
  CALL("Theory::isInterpretedFunction(unsigned)");

  if(func>=Term::SPECIAL_FUNCTOR_LOWER_BOUND) {
    return false;
  }

  return env.signature->getFunction(func)->interpreted() && env.signature->functionArity(func)!=0;
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
 * Assuming @b lit has an interpreted predicate, return its interpretation
 */
Interpretation Theory::interpretPredicate(Literal* lit)
{
  CALL("Theory::interpretFunction");
  ASS(isInterpretedPredicate(lit));

  return interpretPredicate(lit->functor());
}

bool Theory::tryInterpretConstant(TermList trm, IntegerConstantType& res)
{
  CALL("Theory::tryInterpretConstant(TermList,IntegerConstantType)");

  if(!trm.isTerm()) { return false; }
  Term* t = trm.term();
  if(trm.term()->arity()!=0 || t->isSpecial()) { return false; }
  unsigned func = t->functor();
  Signature::Symbol* sym = env.signature->getFunction(func);
  if(!sym->integerConstant()) { return false; }
  res = sym->integerValue();
  return true;
}

bool Theory::tryInterpretConstant(TermList trm, RationalConstantType& res)
{
  CALL("Theory::tryInterpretConstant(TermList,RationalConstantType)");

  if(!trm.isTerm()) { return false; }
  Term* t = trm.term();
  if(trm.term()->arity()!=0 || t->isSpecial()) { return false; }
  unsigned func = t->functor();
  Signature::Symbol* sym = env.signature->getFunction(func);
  if(!sym->rationalConstant()) { return false; }
  res = sym->rationalValue();
  return true;
}

bool Theory::tryInterpretConstant(TermList trm, RealConstantType& res)
{
  CALL("Theory::tryInterpretConstant(TermList,RealConstantType)");

  if(!trm.isTerm()) { return false; }
  Term* t = trm.term();
  if(trm.term()->arity()!=0 || t->isSpecial()) { return false; }
  unsigned func = t->functor();
  Signature::Symbol* sym = env.signature->getFunction(func);
  if(!sym->realConstant()) { return false; }
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

Term* Theory::representIntegerConstant(string str)
{
  CALL("Theory::representIntegerConstant");

  try {
    return Theory::instance()->representConstant(IntegerConstantType(str));
  } catch(ArithmeticException&) {
    NOT_IMPLEMENTED;
//    bool added;
//    unsigned fnNum = env.signature->addFunction(str, 0, added);
//    if(added) {
//      env.signature->getFunction(fnNum)->setType(BaseType::makeType0(Sorts::SRT_INTEGER));
//      env.signature->addToDistinctGroup(fnNum, Signature::INTEGER_DISTINCT_GROUP);
//    }
//    else {
//      ASS(env.signature->getFunction(fnNum))
//    }
  }
}

Term* Theory::representRealConstant(string str)
{
  CALL("Theory::representRealConstant");
  try {
    return Theory::instance()->representConstant(RealConstantType(str));
  } catch(ArithmeticException&) {
    NOT_IMPLEMENTED;
  }
}

/**
 * Return term containing unary function interpreted as @b itp with
 * @b arg as its first argument
 */
Term* Theory::fun1(Interpretation itp, TermList arg)
{
  CALL("Theory::fun1");
  ASS(isFunction(itp));
  ASS_EQ(getArity(itp), 1);

  unsigned fn=theory->getFnNum(itp);
  return Term::create(fn, 1, &arg);
}

/**
 * Return term containing binary function interpreted as @b itp with
 * arguments @b arg1 and @b arg2
 */
Term* Theory::fun2(Interpretation itp, TermList arg1, TermList arg2)
{
  CALL("Theory::fun2");
  ASS(isFunction(itp));
  ASS_EQ(getArity(itp), 2);

  TermList args[]= {arg1, arg2};

  unsigned fn=theory->getFnNum(itp);
  return Term::create(fn, 2, args);
}

/**
 * Return literal containing binary predicate interpreted as @b itp with
 * arguments @b arg1 and @b arg2
 *
 * Equality cannot be created using this function, Term::createEquality has to be used.
 */
Literal* Theory::pred2(Interpretation itp, bool polarity, TermList arg1, TermList arg2)
{
  CALL("Theory::fun2");
  ASS(!isFunction(itp));
  ASS_EQ(getArity(itp), 2);
  ASS_NEQ(itp,EQUAL);

  TermList args[]= {arg1, arg2};

  unsigned pred=theory->getPredNum(itp);
  return Literal::create(pred, 2, polarity, false, args);
}

/**
 * Return number of function that is intepreted as @b itp
 */
unsigned Theory::getFnNum(Interpretation itp)
{
  CALL("Theory::getFnNum");
  ASS(isFunction(itp));
  
  return env.signature->getInterpretingSymbol(itp);
}

/**
 * Return number of predicate that is intepreted as @b itp
 */
unsigned Theory::getPredNum(Interpretation itp)
{
  CALL("Theory::getPredNum");
  ASS(!isFunction(itp));
  
  return env.signature->getInterpretingSymbol(itp);
}

}
















