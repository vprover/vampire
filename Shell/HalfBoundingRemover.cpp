
/*
 * File HalfBoundingRemover.cpp.
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
 * @file HalfBoundingRemover.cpp
 * Implements class HalfBoundingRemover.
 */
#if GNUMP
#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/RCPtr.hpp"

#include "Kernel/Constraint.hpp"
#include "Kernel/Signature.hpp"

#include "Options.hpp"
#include "Statistics.hpp"

#include "HalfBoundingRemover.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

bool HalfBoundingRemover::apply(ConstraintRCList*& lst)
{
  CALL("HalfBoundingRemover::apply");

  scan(lst);

  bool anyRemoved = false;

  anyRemoved |= applyHalfBoundingRemoval(lst);

  if (anyRemoved) {
    reset();
    return true;
  }

  //now we need to apply eliminations one step at a time since they depend
  //on content of _posVars and _negVars which gets invalidated by every change
  //of the constraint list 
  if (env.options->bpAlmostHalfBoundingRemoval()!=Options::AHR_OFF) {
    anyRemoved |= applyAlmostHalfBoundingRemoval(lst,
						 env.options->bpAlmostHalfBoundingRemoval()==Options::AHR_BOUNDS_ONLY);
  }

  if (anyRemoved) {
    reset();
    return true;
  }

  if (env.options->bpFmElimination()) {
    anyRemoved |= applyFMElimination(lst);
  }

  if (anyRemoved) {
    reset();
    return true;
  }

  reset();
  return false;
}

bool HalfBoundingRemover::applyHalfBoundingRemoval(ConstraintRCList*& lst)
{
  CALL("HalfBoundingRemover::applyHalfBoundingRemoval");

  static DHSet<Var> halfBounding;
  halfBounding.reset();

  unsigned varCnt = env.signature->vars();
  for(Var v=0; v<varCnt; v++) {
    size_t posCnt = _v2c.getConstraintCnt(BoundId(v, true));
    size_t negCnt = _v2c.getConstraintCnt(BoundId(v, false));
    if ( (posCnt==0) != (negCnt==0) ) {
      halfBounding.insert(v);
      env.statistics->halfBoundingVariables++;
    }
  }

  bool anyRemoved = false;

  ConstraintRCList::DelIterator cit(lst);
  while(cit.hasNext()) {
    const Constraint& c = *cit.next();

    bool hasHalfBounding = false;
    Constraint::CoeffIterator coeffIt(c.coeffs());
    while(coeffIt.hasNext()) {
      const Constraint::Coeff& coeff = coeffIt.next();
      if (halfBounding.find(coeff.var)) {
	hasHalfBounding = true;
      }
    }

    if (hasHalfBounding) {
      cit.del();
      env.statistics->halfBoundingConstraints++;
      anyRemoved = true;
    }
  }
  return anyRemoved;
}

/**
 * Apply elimination of almost half-bounding variables to one variable and return
 * true. If the rule cannot be applied, return false.
 *
 * This rule eliminates variables that are of one polarity in all but one constraint.
 * If @c boundsOnly is true, the one constraint has to be a bound in order for the
 * variable to be eliminated.
 */
bool HalfBoundingRemover::applyAlmostHalfBoundingRemoval(ConstraintRCList*& lst, bool boundsOnly)
{
  CALL("HalfBoundingRemover::applyAlmostHalfBoundingRemoval");

  unsigned varCnt = env.signature->vars();
  for(Var v=0; v<varCnt; v++) {
    Constraint* posSingleton = _v2c.getOnlyConstraint(BoundId(v, true));
    Constraint* negSingleton = _v2c.getOnlyConstraint(BoundId(v, false));
    if (!posSingleton && !negSingleton) {
      continue;
    }
    if (boundsOnly
       && !( (posSingleton && posSingleton->coeffCnt()==1)
	     || (negSingleton && negSingleton->coeffCnt()==1) )) {
      continue;
    }
    env.statistics->almostHalfBoundingVariables++;
    env.statistics->almostHalfBoundingConstraints += _v2c.getConstraintCnt(v);

    doFMReduction(v, lst);
    return true;
  }
  return false;
}

/**
 * Apply general FM elimination (restricted by the allowed_fm_balance option
 * value) to one variable and return true. If it cannot be applied to any
 * variable, return false.
 */
bool HalfBoundingRemover::applyFMElimination(ConstraintRCList*& lst)
{
  CALL("HalfBoundingRemover::applyFMElimination");

  unsigned allowedBalance = env.options->bpAllowedFMBalance();
  unsigned varCnt = env.signature->vars();
  for(Var v=0; v<varCnt; v++) {
    size_t posCnt = _v2c.getConstraintCnt(BoundId(v, true));
    size_t negCnt = _v2c.getConstraintCnt(BoundId(v, false));
    if (posCnt==0 && negCnt==0) {
      continue;
    }
    if (posCnt*negCnt-posCnt-negCnt>allowedBalance) {
      continue;
    }
    env.statistics->fmRemovedVariables++;

    doFMReduction(v, lst);
    return true;
  }
  return false;
}

void HalfBoundingRemover::doFMReduction(Var v, ConstraintRCList*& constraints)
{
  CALL("HalfBoundingRemover::doFMReduction");

  BoundId posId(v, true);
  BoundId negId(v, false);
  V2CIndex::Iterator pit(_v2c.getConsraintsWithBound(posId));
  while(pit.hasNext()) {
    Constraint& posConstr = *pit.next();
    V2CIndex::Iterator nit(_v2c.getConsraintsWithBound(negId));
    while(nit.hasNext()) {
      Constraint& negConstr = *nit.next();

      ConstraintRCPtr newConstr(Constraint::resolve(v, posConstr, negConstr, false));
      if (!newConstr->isTautology()) {
	ConstraintRCList::push(newConstr, constraints);
	env.statistics->preprocessingFMIntroduced++;
      }
    }
  }

  static DHSet<Constraint*> toRemove;
  toRemove.reset();
  toRemove.loadFromIterator(_v2c.getConsraintsWithBound(posId));
  toRemove.loadFromIterator(_v2c.getConsraintsWithBound(negId));
  env.statistics->preprocessingFMRemoved += toRemove.size();

  ConstraintRCList::DelIterator cit(constraints);
  while(cit.hasNext()) {
    Constraint* c = cit.next().ptr();
    if (toRemove.contains(c)) {
      cit.del();
    }
  }
}

void HalfBoundingRemover::reset()
{
  CALL("HalfBoundingRemover::reset");
  _v2c.reset();
}

void HalfBoundingRemover::scan(ConstraintRCList* lst)
{
  CALL("HalfBoundingRemover::scan");

  _v2c.insert(lst);
}

}
#endif
