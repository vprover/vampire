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

  PredicateSplitPassiveClauseContainer(bool isOutermost, const Shell::Options& opt);
  virtual ~PredicateSplitPassiveClauseContainer();

  void add(Clause* cl);
  void remove(Clause* cl);
  Clause* popSelected();

  /** True if there are no passive clauses */
  bool isEmpty() const
  { ASS(!_queues.empty()); return _queues.back()->isEmpty(); }

  ClauseIterator iterator();

  virtual unsigned size() const { ASS(!_queues.empty()); return _queues.back()->size(); }

private:
  Lib::vvector<std::unique_ptr<AWPassiveClauseContainer>> _queues;
  Lib::vvector<unsigned> _ratios;
  Lib::vvector<float> _cutoffs;
  Lib::vvector<unsigned> _balances;

  unsigned bestQueueHeuristics(Inference* inf) const;

  /*
   * TODO: LRS specific methods and fields
   */
  void updateLimits(long long estReachableCnt);

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

private:
  void onLimitsUpdated();

}; // class PredicateSplitPassiveClauseContainer

};

#endif /* __PredicateSplitPassiveClauseContainer__ */
