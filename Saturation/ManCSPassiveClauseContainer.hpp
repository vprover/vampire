/*
 * File ManCSPassiveClauseContainer.hpp.
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
 * @file ManCSPassiveClauseContainer.hpp
 * Defines the class ManCSPassiveClauseContainer
 */

#ifndef __MANCSPASSIVECLAUSECONTAINER__
#define __MANCSPASSIVECLAUSECONTAINER__

#include <vector>
#include "Kernel/Clause.hpp"
#include "ClauseContainer.hpp"
#include "Kernel/ClauseQueue.hpp"

namespace Saturation {

using namespace Kernel;

/*
 * Subclass of PassiveClauseContainer for manual selection of clauses
 * asks in each iteration the user to pick the id of the clause which should be activated next
 */
class ManCSPassiveClauseContainer : public PassiveClauseContainer
{
public:
  CLASS_NAME(ManCSPassiveClauseContainer);
  USE_ALLOCATOR(ManCSPassiveClauseContainer);

  ManCSPassiveClauseContainer(bool isOutermost, const Shell::Options& opt) : PassiveClauseContainer(isOutermost, opt) {}
  virtual ~ManCSPassiveClauseContainer(){}
  
  virtual unsigned size() const;
  bool isEmpty() const;
  ClauseIterator iterator();

  void add(Clause* cl);
  void remove(Clause* cl);

  Clause* popSelected();
  
private:
  std::vector<Clause*> clauses;

  /*
   * LRS specific methods and fields
   */
public:
  virtual void updateLimits(long long estReachableCnt) {};

  virtual bool ageLimited() const { return false; }
  virtual bool weightLimited() const { return false; }

  virtual bool fulfilsAgeLimit(Clause* c) const { return true; }
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool fulfilsAgeLimit(unsigned age, unsigned w, unsigned numeralWeight, bool derivedFromGoal, Inference* inference) const { return true; }
  virtual bool fulfilsWeightLimit(Clause* cl) const { return true; }
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  virtual bool fulfilsWeightLimit(unsigned w, unsigned numeralWeight, bool derivedFromGoal, unsigned age, Inference* inference) const { return true; }

  virtual bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const { return true; }
};

}

#endif /* __MANCSPASSIVECLAUSECONTAINER__ */
