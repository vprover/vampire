
/*
 * File EquivalentVariableRemover.cpp.
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
 * @file EquivalentVariableRemover.cpp
 * Implements class EquivalentVariableRemover.
 */
#if GNUMP

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/RCPtr.hpp"

#include "Kernel/Constraint.hpp"
#include "Kernel/Signature.hpp"

#include "Statistics.hpp"

#include "EquivalentVariableRemover.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

EquivalentVariableRemover::EquivalentVariableRemover()
 : _eqClasses(env.signature->vars())
{
  CALL("EquivalentVariableRemover::EquivalentVariableRemover");

  reset();
}

struct EquivalentVariableRemover::VarMapper
{
  VarMapper(EquivalentVariableRemover& parent) : _parent(parent) {}

  Constraint::Coeff operator()(const Constraint::Coeff& coeff)
  {
    CALL("EquivalentVariableRemover::VarMapper::operator()");

    return Constraint::Coeff(_parent.getRoot(coeff.var), coeff.value);
  }

  EquivalentVariableRemover& _parent;
};

bool EquivalentVariableRemover::apply(ConstraintRCList*& lst)
{
  CALL("EquivalentVariableRemover::apply");

  scan(lst);
  if(!_haveEquivalences) {
    reset();
    return false;
  }
  bool anyRemoved = false;
  ConstraintRCList::DelIterator cit(lst);
  while(cit.hasNext()) {
    Constraint& c = *cit.next();
    if(remainsSame(c)) {
      continue;
    }
    VirtualIterator<Constraint::Coeff> newCoeffs = pvi( getMappingIterator(c.coeffs(), VarMapper(*this)) );
    ConstraintRCPtr replacement(
	Constraint::fromBagIterator(c.type(), newCoeffs, c.freeCoeff()));
    if(replacement->isTautology()) {
      cit.del();
    }
    else {
      cit.replace(replacement);
    }
    anyRemoved = true;
  }
  ASS(anyRemoved);
  reset();
  return anyRemoved;
}

void EquivalentVariableRemover::reset()
{
  CALL("EquivalentVariableRemover::reset");

  _pairs.reset();
  _eqClasses.reset();
  _haveEquivalences = false;
}

bool EquivalentVariableRemover::remainsSame(Constraint& c)
{
  CALL("EquivalentVariableRemover::remainsSame");

  Constraint::CoeffIterator cit = c.coeffs();
  while(cit.hasNext()) {
    if(!remainsSame(cit.next().var)) {
      return false;
    }
  }
  return true;
}

void EquivalentVariableRemover::scan(ConstraintRCList* lst)
{
  CALL("EquivalentVariableRemover::scan");

  ConstraintRCList::Iterator it(lst);
  while(it.hasNext()) {
    const Constraint& c = *it.next();
    if(c.coeffCnt()!=2 || !c.freeCoeff().isZero() || c.type()!=CT_GREQ
	|| c[0].value.abs()!=CoeffNumber::one()
	|| c[1].value.abs()!=CoeffNumber::one()
	|| (c[0].value*c[1].value)!=CoeffNumber::minusOne()) {
      continue;
    }

    VarPair vp(c[0].var, c[1].var);
    PairStatus newStatus = c[0].isPositive() ? FIRST_POS : FIRST_NEG;
    PairStatus oldStatus;
    if(_pairs.find(vp, oldStatus)) {
      if(oldStatus == -newStatus) {
	_pairs.set(vp, BOTH);
	_haveEquivalences = true;
	if(_eqClasses.doUnion(vp.first, vp.second)) {
	  env.statistics->equivalentVariables++;
	}
      }
    }
    else {
      ALWAYS( _pairs.insert(vp, newStatus) );
    }
  }
}

}
#endif //GNUMP

