
/*
 * File Limits.cpp.
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
 * @file Limits.cpp
 * Implements class Limits.
 */

#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"


#include "Limits.hpp"

namespace Saturation
{

bool Limits::fulfilsAgeLimit(Clause* cl) const
{
  return fulfilsAgeLimit(cl->age());
}

bool Limits::fulfilsAgeLimit(unsigned age) const
{
  return age <= _ageSelectionMaxAge;
}

bool Limits::fulfilsWeightLimit(Clause* cl) const
{
  return cl->weightForClauseSelection(_opt) <= _weightSelectionMaxWeight;
}

bool Limits::fulfilsWeightLimit(unsigned int w, unsigned int numeralWeight, bool derivedFromGoal) const
{
  float weightForClauseSelection = Clause::computeWeightForClauseSelection(w, numeralWeight, derivedFromGoal, _opt);
  return weightForClauseSelection <= _weightSelectionMaxWeight;
}

bool Limits::childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const
{
  if (cl->age() == _ageSelectionMaxAge)
  {
    // clauses inferred from the clause as generating inferences will be over age limit...
    int maxSelWeight=0;
    for(unsigned i=0;i<upperBoundNumSelLits;i++) {
      maxSelWeight=max((int)(*cl)[i]->weight(),maxSelWeight);
    }
    // TODO: this lower bound is not correct:
    //       if Avatar is used, then the child-clause could become splittable,
    //       in which case we don't know any lower bound on the resulting components.
    unsigned weightLowerBound = cl->weight() - maxSelWeight; // heuristic: we assume that at most one literal will be removed from the clause.
    unsigned numeralWeight = 0; // heuristic: we don't know the numeral weight of the child, and conservatively assume that it is 0.
    bool derivedFromGoal = true; // heuristic: we have to cover the case where the child has another parent which is a goal-clause. We conservatively assume that the result is a goal-clause.
    if (!fulfilsWeightLimit(weightLowerBound, numeralWeight, derivedFromGoal)) {
      //and also over weight limit
      return false;
    }
  }
  return true;
}

bool Limits::setLimits(int newMaxAge, int newMaxWeight)
{
  CALL("Limits::setLimits");

  bool atLeastOneTightened = false;
  if(_ageSelectionMaxAge!=newMaxAge) {
    if(newMaxAge < _ageSelectionMaxAge) {
      atLeastOneTightened = true;
    }
    _ageSelectionMaxAge=newMaxAge;
  }
  if(_weightSelectionMaxWeight!=newMaxWeight) {
    if(newMaxWeight < _weightSelectionMaxWeight) {
      atLeastOneTightened = true;
    }
    _weightSelectionMaxWeight=newMaxWeight;
  }
  return atLeastOneTightened;
}


}
