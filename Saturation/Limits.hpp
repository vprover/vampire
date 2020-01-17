
/*
 * File Limits.hpp.
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
 * @file Limits.hpp
 * Defines class Limits
 *
 */

#ifndef __Limits__
#define __Limits__

#include "Forwards.hpp"

#include "Lib/Event.hpp"

#include "Kernel/Clause.hpp"


namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;

typedef PlainEvent LimitsChangeEvent;

class Limits
{
public:
  CLASS_NAME(Limits);
  USE_ALLOCATOR(Limits);

  LimitsChangeEvent changedEvent;

  Limits(const Options& opt) : _opt(opt) {}

  virtual ~Limits() {}

  virtual bool ageLimited() const = 0;
  virtual bool weightLimited() const = 0;

  virtual bool fulfilsAgeLimit(Clause* c) const = 0;
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool fulfilsAgeLimit(unsigned age, unsigned w, unsigned numeralWeight, bool derivedFromGoal, Inference* inference) const = 0;
  virtual bool fulfilsWeightLimit(Clause* cl) const = 0;
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool fulfilsWeightLimit(unsigned w, unsigned numeralWeight, bool derivedFromGoal, unsigned age, Inference* inference) const = 0;

  virtual bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const = 0;
  
protected:
  const Options& _opt;
};

class AWPassiveClauseContainerLimits : public Limits
{
public:
  CLASS_NAME(AWPassiveClauseContainerLimits);
  USE_ALLOCATOR(AWPassiveClauseContainerLimits);

  AWPassiveClauseContainerLimits(const Options& opt) : Limits(opt), _ageSelectionMaxAge(UINT_MAX), _ageSelectionMaxWeight(UINT_MAX), _weightSelectionMaxWeight(UINT_MAX), _weightSelectionMaxAge(UINT_MAX) {}
  ~AWPassiveClauseContainerLimits() {}

  virtual bool ageLimited() const { return _ageSelectionMaxAge != UINT_MAX && _ageSelectionMaxWeight != UINT_MAX; }
  virtual bool weightLimited() const { return _weightSelectionMaxWeight != UINT_MAX && _weightSelectionMaxAge != UINT_MAX; }

  virtual bool fulfilsAgeLimit(Clause* c) const;
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool fulfilsAgeLimit(unsigned age, unsigned w, unsigned numeralWeight, bool derivedFromGoal, Inference* inference) const;
  virtual bool fulfilsWeightLimit(Clause* cl) const;
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool fulfilsWeightLimit(unsigned w, unsigned numeralWeight, bool derivedFromGoal, unsigned age, Inference* inference) const;

  virtual bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const;

  // returns whether at least one of the limits was tightened
  bool setLimits(unsigned newAgeSelectionMaxAge, unsigned newAgeSelectionMaxWeight, unsigned newWeightSelectionMaxWeight, unsigned newWeightSelectionMaxAge);

private:
  unsigned _ageSelectionMaxAge;
  unsigned _ageSelectionMaxWeight;
  unsigned _weightSelectionMaxWeight;
  unsigned _weightSelectionMaxAge;
};

};

#endif /*__Limits__*/
