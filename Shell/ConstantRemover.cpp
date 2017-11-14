
/*
 * File ConstantRemover.cpp.
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
 * @file ConstantRemover.cpp
 * Implements class ConstantRemover.
 */
#if GNUMP

#include "Lib/Environment.hpp"

#include "Kernel/Constraint.hpp"
#include "Kernel/Signature.hpp"

#include "Statistics.hpp"

#include "ConstantRemover.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

ConstantRemover::ConstantRemover()
  : _varCnt(env.signature->vars())
{
  reset();
}

bool ConstantRemover::apply(ConstraintRCList*& lst)
{
  CALL("ConstantRemover::apply");

  if(!scan(lst)) {
    reset();
    return false;
  }

  bool anyUpdated = false;
  ConstraintRCList::DelIterator cit(lst);
  while(cit.hasNext()) {
    ConstraintRCPtr c0 = cit.next();
    ConstraintRCPtr c = c0;
    Constraint::CoeffIterator coeffIt(c0->coeffs());
    while(coeffIt.hasNext()) {
      const Constraint::Coeff& coeff = coeffIt.next();
      Var v = coeff.var;
      const DefiningPair& d = _vals[v];
      if(!d.isTight) {
	continue;
      }
      bool needsLeft = coeff.isNegative();
      c = ConstraintRCPtr(Constraint::resolve(v, *c, needsLeft ? *d.left : *d.right, false));
    }
    if(c!=c0) {
      env.statistics->updatedByConstantPropagation++;
      anyUpdated = true;
      if(c->isTautology()) {
        cit.del();
      }
      else {
	cit.replace(c);
      }
    }
  }
  ASS(anyUpdated); //at least the constant definition itself should be always removed

  reset();
  return anyUpdated;
}

void ConstantRemover::reset()
{
  CALL("ConstantRemover::reset");

  _vals.init(_varCnt, DefiningPair());
}

bool ConstantRemover::scan(ConstraintRCList* lst)
{
  CALL("ConstantRemover::scan");

  ConstraintRCList::Iterator cit(lst);
  while(cit.hasNext()) {
    ConstraintRCPtr c = cit.next();
    if(c->coeffCnt()!=1 || c->type()!=CT_GREQ) {
      continue;
    }
    const Constraint::Coeff& coeff = (*c)[0];
    Var v = coeff.var;
    bool left = coeff.isPositive();

    //Here we simply assign into appropriate field in the _vals array.
    //We ignore the fact that there can be multiple bounds of the
    //same type for one variable. We can do this because the
    //SubsumptionRemover will eventually ensure there will remain only
    //the strictest bound.
    if(left) {
      _vals[v].left = c;
    }
    else {
      _vals[v].right = c;
    }
  }

  bool haveConstant = false;
  for(Var v = 0; v<_varCnt; v++) {
    DefiningPair& d = _vals[v];
    if(!d.left || !d.right || d.left->freeCoeff()!=-d.right->freeCoeff()
	|| (*d.left)[0].value!=-(*d.right)[0].value) {
      continue;
    }
    d.isTight = true;
    haveConstant = true;
    env.statistics->constantVariables++;
  }

  return haveConstant;
}


}
#endif //GNUMP

