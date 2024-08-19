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
  bool mayBeAbleToDiscriminateChildrenOnLimits() const override { return false; }
  bool allChildrenNecessarilyExceedLimits(Clause*, unsigned) const override { return false; }

  bool mayBeAbleToDiscriminateClausesUnderConstructionOnLimits() const override { return false; }
  bool exceedsAgeLimit(unsigned, const Inference&, bool&) const override { return false; }
  bool exceedsWeightLimit(unsigned, unsigned, const Inference&) const override { return false; }

  bool limitsActive() const override { return false; }
  bool exceedsAllLimits(Clause*) const override { return false; }
};

}

#endif /* __MANCSPASSIVECLAUSECONTAINER__ */
