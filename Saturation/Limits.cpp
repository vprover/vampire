
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
  // don't want to reuse fulfilsAgeLimit(unsigned age,..) here, since we don't want to recompute weightForClauseSelection
  unsigned age = cl->age();
  unsigned weightForClauseSelection = cl->weightForClauseSelection(_opt);
  return age <= _ageSelectionMaxAge || (age == _ageSelectionMaxAge && weightForClauseSelection <= _ageSelectionMaxWeight);
}

bool Limits::fulfilsAgeLimit(unsigned age, unsigned w, unsigned numeralWeight, bool derivedFromGoal) const
{
  unsigned weightForClauseSelection = Clause::computeWeightForClauseSelection(w, numeralWeight, derivedFromGoal, _opt);
  return age <= _ageSelectionMaxAge || (age == _ageSelectionMaxAge && weightForClauseSelection <= _ageSelectionMaxWeight);
}

bool Limits::fulfilsWeightLimit(Clause* cl) const
{
  // don't want to reuse fulfilsWeightLimit(unsigned w,..) here, since we don't want to recompute weightForClauseSelection
  unsigned weightForClauseSelection = cl->weightForClauseSelection(_opt);
  unsigned age = cl->age();
  return weightForClauseSelection <= _weightSelectionMaxWeight || (weightForClauseSelection == _weightSelectionMaxWeight && age <= _weightSelectionMaxAge);
}

bool Limits::fulfilsWeightLimit(unsigned w, unsigned numeralWeight, bool derivedFromGoal, unsigned age) const
{
  unsigned weightForClauseSelection = Clause::computeWeightForClauseSelection(w, numeralWeight, derivedFromGoal, _opt);
  return weightForClauseSelection <= _weightSelectionMaxWeight || (weightForClauseSelection == _weightSelectionMaxWeight && age <= _weightSelectionMaxAge);
}

bool Limits::childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const
{
  if (cl->age() == _ageSelectionMaxAge)
  {
    // clauses inferred from the clause as generating inferences will be over age limit...
    unsigned childAge = cl->age() + 1;
    
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
    if (!fulfilsWeightLimit(weightLowerBound, numeralWeight, derivedFromGoal, childAge)) {
      //and also over weight limit
      return false;
    }
  }
  return true;
}

bool Limits::setLimits(unsigned newAgeSelectionMaxAge, unsigned newAgeSelectionMaxWeight, unsigned newWeightSelectionMaxWeight, unsigned newWeightSelectionMaxAge)
{
  CALL("Limits::setLimits");

  bool atLeastOneTightened = false;
  if(newAgeSelectionMaxAge != _ageSelectionMaxAge || newAgeSelectionMaxWeight != _ageSelectionMaxWeight) {
    if(newAgeSelectionMaxAge < _ageSelectionMaxAge) {
      atLeastOneTightened = true;
    } else if (newAgeSelectionMaxAge == _ageSelectionMaxAge && newAgeSelectionMaxWeight < _ageSelectionMaxWeight) {
      atLeastOneTightened = true;
    }
    _ageSelectionMaxAge=newAgeSelectionMaxAge;
    _ageSelectionMaxWeight=newAgeSelectionMaxWeight;
  }
  if(newWeightSelectionMaxWeight != _weightSelectionMaxWeight || newWeightSelectionMaxAge != _weightSelectionMaxAge) {
    if(newWeightSelectionMaxWeight < _weightSelectionMaxWeight) {
      atLeastOneTightened = true;
    } else if (newWeightSelectionMaxWeight == _weightSelectionMaxWeight && newWeightSelectionMaxAge < _weightSelectionMaxAge) {
      atLeastOneTightened = true;
    }
    _weightSelectionMaxWeight=newWeightSelectionMaxWeight;
    _weightSelectionMaxAge=newWeightSelectionMaxAge;
  }
  return atLeastOneTightened;
}

}
