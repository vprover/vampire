/*
 * File PredicateSplitPassiveClauseContainer.hpp.
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

#ifndef __PredicateSplitPassiveClauseContainer__
#define __PredicateSplitPassiveClauseContainer__

#include <memory>
#include <vector>
#include "Lib/Allocator.hpp"
#include "ClauseContainer.hpp"
#include "AWPassiveClauseContainer.hpp"
#include "Lib/STL.hpp"

namespace Saturation {
class PredicateSplitPassiveClauseContainer
: public PassiveClauseContainer
{
public:
  CLASS_NAME(PredicateSplitPassiveClauseContainer);
  USE_ALLOCATOR(PredicateSplitPassiveClauseContainer);

  PredicateSplitPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name);
  virtual ~PredicateSplitPassiveClauseContainer();

  void add(Clause* cl);
  void remove(Clause* cl);
  Clause* popSelected();

  /** True if there are no passive clauses */
  bool isEmpty() const;

  virtual unsigned sizeEstimate() const;

private:
  Lib::vvector<std::unique_ptr<AWPassiveClauseContainer>> _queues;
  Lib::vvector<unsigned> _ratios;
  Lib::vvector<float> _cutoffs;
  Lib::vvector<unsigned> _balances;

  unsigned bestQueueHeuristics(Inference* inf) const;

  /*
   * LRS specific methods for computation of Limits
   */
public:
  virtual void simulationInit();
  virtual bool simulationHasNext();
  virtual void simulationPopSelected();

  // returns whether at least one of the limits was tightened
  virtual bool setLimitsToMax();
  // returns whether at least one of the limits was tightened
  virtual bool setLimitsFromSimulation();

  virtual void onLimitsUpdated();

private:
  Lib::vvector<unsigned> _simulationBalances;

  /*
   * LRS specific methods and fields for usage of limits
   */
public:
  virtual bool ageLimited() const;
  virtual bool weightLimited() const;

  virtual bool fulfilsAgeLimit(Clause* cl) const;
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool fulfilsAgeLimit(unsigned age, unsigned w, unsigned numeralWeight, bool derivedFromGoal, Inference* inference) const;
  virtual bool fulfilsWeightLimit(Clause* cl) const;
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool fulfilsWeightLimit(unsigned w, unsigned numeralWeight, bool derivedFromGoal, unsigned age, Inference* inference) const;

  virtual bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const;
  
}; // class PredicateSplitPassiveClauseContainer

};

#endif /* __PredicateSplitPassiveClauseContainer__ */
