
/*
 * File Assignment.cpp.
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
 * @file Assignment.cpp
 * Implements class Assignment.
 */
#if GNUMP
#include "Lib/Metaiterators.hpp"

#include "Assignment.hpp"

namespace Kernel
{

VarIterator Assignment::getAssignedVars() const
{
  CALL("Assignment::getAssignedVars");

  return pvi( getStaticCastIterator<Var>(AssignmentMap::KeyIterator(_data)) );
}

/**
 * Evaluate sum of coefficients in the @c coeffs iterator
 *
 * All variables in the @c coeffs iterator must be present in the assignment.
 */
BoundNumber Assignment::evalCoeffs(Constraint::CoeffIterator coeffs) 
{
  CALL("Assignment::evalCoeffs");

  BoundNumber res = BoundNumber::zero();
  while(coeffs.hasNext()) {
    Constraint::Coeff coeff = coeffs.next();
    ASS(isAssigned(coeff.var));
    res+=BoundNumber(coeff.value) * (*this)[coeff.var];
  }
  return res;
}

/**
 * Assert that constraint @c c is satisfied by the assignment
 */
bool Assignment::isSatisfied(const Constraint* c)
{
  CALL("Assignment::isSatisfied(const Constraint*)");

  BoundNumber lhs = evalCoeffs(c->coeffs());
  BoundNumber rhs(c->freeCoeff());

  switch(c->type()) {
  case CT_EQ:
    return lhs==rhs;
  case CT_GR:
    return lhs>rhs;
  case CT_GREQ:
    return lhs>=rhs;
  default:
    ASSERTION_VIOLATION;
    return false;
  }
}

/**
 * Assert that constraints in the @c constraints list are
 * satisfied by the assignment
 */
bool Assignment::isSatisfied(Kernel::ConstraintList* constraints)
{
  CALL("Assignment::isSatisfied(ConstraintList*)");

  ConstraintList::Iterator cit(constraints);
  while(cit.hasNext()) {
    if(!isSatisfied(cit.next())) {
      return false;
    }
  }
  return true;
}


#if VDEBUG
/**
 * Assert that constraint @c c is satisfied by the assignment
 */
void Assignment::assertSatisfied(const Constraint* c)
{
  CALL("Assignment::assertSatisfied(const Constraint*)");

  BoundNumber lhs = evalCoeffs(c->coeffs());
  BoundNumber rhs(c->freeCoeff());

  switch(c->type()) {
  case CT_EQ:
    ASS_REP2(lhs==rhs, c->toString(), lhs);
    break;
  case CT_GR:
    ASS_REP2(lhs>rhs, c->toString(), lhs);
    break;
  case CT_GREQ:
    ASS_REP2(lhs>=rhs, c->toString(), lhs);
    break;
  }
}

/**
 * Assert that constraints in the @c constraints list are
 * satisfied by the assignment
 */
void Assignment::assertSatisfied(ConstraintList* constraints)
{
  CALL("Assignment::assertSatisfied(ConstraintList*)");

  ConstraintList::Iterator cit(constraints);
  while(cit.hasNext()) {
    assertSatisfied(cit.next());
  }
}
#endif

}
#endif //GNUMP
