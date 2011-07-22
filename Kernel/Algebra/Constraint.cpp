/**
 * @file Constraint.cpp
 * Implements class Constraint.
 */

#include "Kernel/Theory.hpp"

#include "Constraint.hpp"

namespace Kernel
{
namespace Algebra
{
#if 0
/**
 * Return true iff @b lit represents a constraint
 */
bool Constraint::isConstraint(Literal* lit)
{
  CALL("Constraint::isConstraint");

  return lit->isEquality() || theory->isInterpretedPredicate(lit, Theory::LESS_EQUAL) ||
      theory->isInterpretedPredicate(lit, Theory::INT_LESS_EQUAL);
}

/**
 * Build a constraint object from literal @b lit.
 * If @b negate is true, we consider the polarity of @b lit
 * to be opposite.
 */
Constraint::Constraint(Literal* lit, bool negate)
: _simplified(false)
{
  CALL("Constraint::Constraint");
  ASS(isConstraint(lit));

  _inequality=!lit->isEquality();
  _negative=lit->isNegative();
  _integer=theory->isInterpretedPredicate(lit, Theory::INT_LESS_EQUAL);

  TermList t1=*lit->nthArgument(0);
  TermList t2=*lit->nthArgument(1);

  bool swapSign=_negative;

  if(t1==theory->zero()) {
    swap(t1,t2);
    swapSign^=1;
  }
  _pol.init(t1);
  if(t2!=theory->zero()) {
    Polynomial pol2(t2);
    _pol.subtract(pol2);
  }

  _simplified|=_pol.mergeSummands();
  _simplified|=_pol.reduceCoeffitients();

  if(_inequality && swapSign) {
    if(!_pol.negate()) {
      //this is just for the rare case that there would be an overflow during negating the polynomial
      TermList neg=TermList(theory->fun1(Theory::UNARY_MINUS, _pol.toTerm()));
      _pol.reset();
      _pol.init(neg);
    }
  }
}

/**
 * Attempt various simplifications and return true if some were performed
 */
bool Constraint::simplify()
{
  CALL("Constraint::simplify");

  if(doSimplifications()) {
    _simplified=true;
    return true;
  }
  return false;
}

/**
 * Attempt various simplifications and return true if some were performed
 */
bool Constraint::doSimplifications(ArithmeticKB* kb)
{
  CALL("Constraint::doSimplifications");

  if(!_inequality) {
    if(_pol.size()==1 && _pol[0].coef!=0) {
      _pol[0].coef=1;
      return true;
    }
  }

  return false;
}
#endif
}
}
