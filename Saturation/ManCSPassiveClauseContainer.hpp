/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
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
class ManCSPassiveClauseContainer final : public PassiveClauseContainer
{
public:
  CLASS_NAME(ManCSPassiveClauseContainer);
  USE_ALLOCATOR(ManCSPassiveClauseContainer);

  ManCSPassiveClauseContainer(bool isOutermost, const Shell::Options& opt) : PassiveClauseContainer(isOutermost, opt) {}
  ~ManCSPassiveClauseContainer() final{}
  
  unsigned sizeEstimate() const final;
  bool isEmpty() const final;
  void add(Clause* cl) final;
  void remove(Clause* cl) final;
  Clause* popSelected() final;
  
private:
  std::vector<Clause*> clauses;

  /*
   * LRS specific methods for computation of Limits
   */
public:
  void simulationInit() final {}
  bool simulationHasNext() final { return false; }
  void simulationPopSelected() final {}

  // returns whether at least one of the limits was tightened
  bool setLimitsToMax() final { return false; }
  // returns whether at least one of the limits was tightened
  bool setLimitsFromSimulation() final { return false; }

  void onLimitsUpdated() final {}

  /*
   * LRS specific methods and fields for usage of limits
   */
  bool ageLimited() const final { return false; }
  bool weightLimited() const final { return false; }

  bool fulfilsAgeLimit(Clause* c) const final { return true; }
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.

  bool fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const final { return true; }
  bool fulfilsWeightLimit(Clause* cl) const final { return true; }
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  bool fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const final { return true; }

  bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const final { return true; }
};

}

#endif /* __MANCSPASSIVECLAUSECONTAINER__ */
