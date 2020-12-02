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
class ManCSPassiveClauseContainer : public PassiveClauseContainer
{
public:
  CLASS_NAME(ManCSPassiveClauseContainer);
  USE_ALLOCATOR(ManCSPassiveClauseContainer);

  ManCSPassiveClauseContainer(bool isOutermost, const Shell::Options& opt) : PassiveClauseContainer(isOutermost, opt) {}
  virtual ~ManCSPassiveClauseContainer(){}
  
  unsigned sizeEstimate() const override;
  bool isEmpty() const override;
  void add(Clause* cl) override;
  void remove(Clause* cl) override;
  Clause* popSelected() override;
  
private:
  std::vector<Clause*> clauses;

  /*
   * LRS specific methods for computation of Limits
   */
public:
  void simulationInit() override {}
  bool simulationHasNext() override { return false; }
  void simulationPopSelected() override {}

  // returns whether at least one of the limits was tightened
  bool setLimitsToMax() override { return false; }
  // returns whether at least one of the limits was tightened
  bool setLimitsFromSimulation() override { return false; }

  void onLimitsUpdated() override {}

  /*
   * LRS specific methods and fields for usage of limits
   */
  bool ageLimited() const override { return false; }
  bool weightLimited() const override { return false; }

  bool fulfilsAgeLimit(Clause* c) const override { return true; }
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.

  bool fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { return true; }
  bool fulfilsWeightLimit(Clause* cl) const override { return true; }
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  bool fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { return true; }

  bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const override { return true; }
};

}

#endif /* __MANCSPASSIVECLAUSECONTAINER__ */
