/**
 * @file Theory.cpp
 * Implements class Theory.
 */

#include <math.h>

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Kernel/Signature.hpp"

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

  ALWAYS(Int::stringToInt(str, _val));

  //we want the string representation to be cannonical
  ASS_EQ(str, toString());
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

  return "("+numStr+"/"+denStr+")";
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

///////////////////////
// RealConstantType
//

RealConstantType::RealConstantType(const string& number)
{
  CALL("RealConstantType::RealConstantType");

  double numDbl;
  ALWAYS(Int::stringToDouble(number, numDbl));
  InnerType denominator = 1;
  while(floor(numDbl)!=numDbl) {
    denominator = denominator*10;
    numDbl *= 10;
  }

  InnerType::InnerType numerator = static_cast<InnerType::InnerType>(numDbl);
  if(numerator!=numDbl) {
    //the numerator part of double doesn't fit inside the inner integer type
    throw ArithmeticException();
  }
  init(numerator, denominator);
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
: _zero(0), _one(0), _minusOne(0)
{

}

/**
 * Return arity of the symbol that is interpreted by Interpretation
 * @b i.
 */
unsigned Theory::getArity(Interpretation i)
{
  CALL("Signature::InterpretedSymbol::getArity");
  ASS_L(i,(int)interpretationElementCount);

  switch(i) {
  case SUCCESSOR:
  case UNARY_MINUS:
    return 1;

  case PLUS:
  case MINUS:
  case MULTIPLY:
  case DIVIDE:
  case INT_DIVIDE:
  case EQUAL:
  case GREATER:
  case GREATER_EQUAL:
  case LESS:
  case LESS_EQUAL:
  case INT_GREATER:
  case INT_GREATER_EQUAL:
  case INT_LESS:
  case INT_LESS_EQUAL:
    return 2;
  }
  ASSERTION_VIOLATION;
}

/**
 * Return true iff the symbol that is interpreted by Interpretation
 * is a function (false is returned for predicates)
 */
bool Theory::isFunction(Interpretation i)
{
  CALL("Signature::InterpretedSymbol::isFunction");
  ASS_L(i,(int)interpretationElementCount);

  switch(i) {
  case SUCCESSOR:
  case UNARY_MINUS:
  case PLUS:
  case MINUS:
  case MULTIPLY:
  case DIVIDE:
  case INT_DIVIDE:
    return true;

  case EQUAL:
  case GREATER:
  case GREATER_EQUAL:
  case LESS:
  case LESS_EQUAL:
  case INT_GREATER:
  case INT_GREATER_EQUAL:
  case INT_LESS:
  case INT_LESS_EQUAL:
    return false;
  }
  ASSERTION_VIOLATION;
}

/**
 * Return true iff the symbol that is interpreted by Interpretation
 * is inequality predicate
 */
bool Theory::isInequality(Interpretation i)
{
  CALL("Signature::InterpretedSymbol::isInequality");
  ASS_L(i,(int)interpretationElementCount);

  switch(i) {
  case GREATER:
  case GREATER_EQUAL:
  case LESS:
  case LESS_EQUAL:
  case INT_GREATER:
  case INT_GREATER_EQUAL:
  case INT_LESS:
  case INT_LESS_EQUAL:
    return true;
  default:
    return false;
  }
  ASSERTION_VIOLATION;
}

/**
 * Return term with constant representing number 0
 */
TermList Theory::zero()
{
  if(!_zero) {
    _zero=getRepresentation(0);
  }
  return TermList(_zero);
}

/**
 * Return term with constant representing number 1
 */
TermList Theory::one()
{
  if(!_one) {
    _one=getRepresentation(1);
  }
  return TermList(_one);
}

/**
 * Return term with constant representing number -1
 */
TermList Theory::minusOne()
{
  if(!_minusOne) {
    _minusOne=getRepresentation(-1);
  }
  return TermList(_minusOne);
}

/**
 * Return true iff @b t is an interpreted constant
 */
bool Theory::isInterpretedConstant(Term* t)
{
  CALL("Theory::isInterpretedConstant(Term*)");

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
 * Return true iff @b lit has an interpreted predicate
 */
bool Theory::isInterpretedPredicate(Literal* lit)
{
  CALL("Theory::isInterpretedPredicate");

  return env.signature->getPredicate(lit->functor())->interpreted();
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

/**
 * Return true iff @b t is an interpreted function
 */
bool Theory::isInterpretedFunction(Term* t)
{
  CALL("Theory::isInterpretedFunction(Term*)");

  return t->arity()!=0 && env.signature->getFunction(t->functor())->interpreted();
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

  return t->arity()!=0 && env.signature->getFunction(t->functor())->interpreted() &&
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

/**
 * Assuming @b t is an interpreted function, return its interpretation
 */
Interpretation Theory::interpretFunction(Term* t)
{
  CALL("Theory::interpretFunction");
  ASS(isInterpretedFunction(t));

  return static_cast<Signature::InterpretedSymbol*>(env.signature->getFunction(t->functor()))
      ->getInterpretation();
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

/**
 * Assuming @b lit has an interpreted predicate, return its interpretation
 */
Interpretation Theory::interpretPredicate(Literal* lit)
{
  CALL("Theory::interpretFunction");
  ASS(isInterpretedPredicate(lit));

  return static_cast<Signature::InterpretedSymbol*>(env.signature->getPredicate(lit->functor()))
      ->getInterpretation();
}

/**
 * Assuming @b t is an interpreted constant, return value of this constant
 */
InterpretedType Theory::interpretConstant(Term* t)
{
  CALL("Theory::interpretConstant");
  ASS(isInterpretedConstant(t));

  Signature::InterpretedSymbol* sym =
      static_cast<Signature::InterpretedSymbol*>(env.signature->getFunction(t->functor()));

  return sym->getValue();
}

/**
 * Assuming @b t is an interpreted constant, return value of this constant
 */
InterpretedType Theory::interpretConstant(TermList t)
{
  CALL("Theory::interpretConstant(TermList)");
  ASS(t.isTerm());

  return interpretConstant(t.term());
}

/**
 * Return term containing the constant of value @b val
 */
Term* Theory::getRepresentation(InterpretedType val)
{
  CALL("Theory::getRepresentation");

  Term** pRes;

  if(!_constants.getValuePtr(val, pRes)) {
    return *pRes;
  }

  int functor=env.signature->addInterpretedConstant(val);

  *pRes=Term::create(functor, 0, 0);
  return *pRes;
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
 */
Literal* Theory::pred2(Interpretation itp, bool polarity, TermList arg1, TermList arg2)
{
  CALL("Theory::fun2");
  ASS(!isFunction(itp));
  ASS_EQ(getArity(itp), 2);

  if(itp==EQUAL) {
    return Literal::createEquality(polarity, arg1, arg2);
  }

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
















