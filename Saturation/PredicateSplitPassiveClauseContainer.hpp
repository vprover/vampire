/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
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

  PredicateSplitPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues, Lib::vvector<float> cutoffs, Lib::vvector<int> ratios, bool layeredArrangement);
  virtual ~PredicateSplitPassiveClauseContainer();

  void add(Clause* cl) override;
  void remove(Clause* cl) override;
  Clause* popSelected() override;
  bool isEmpty() const override; /** True if there are no passive clauses */
  unsigned sizeEstimate() const override;

private:
  Lib::vvector<std::unique_ptr<PassiveClauseContainer>> _queues;
  Lib::vvector<float> _cutoffs;
  Lib::vvector<unsigned> _ratios;  
  Lib::vvector<unsigned> _balances;
  bool _layeredArrangement; // if set to true, queues are arranged as multi-split-queues. if false, queues use a tammet-style arrangement.

  unsigned bestQueue(float featureValue) const;

  virtual float evaluateFeature(Clause* cl) const = 0;
  virtual float evaluateFeatureEstimate(unsigned numPositiveLiterals, const Inference& inf) const = 0;

  /*
   * LRS specific methods for computation of Limits
   */
public:
  void simulationInit() override;
  bool simulationHasNext() override;
  void simulationPopSelected() override;

  // returns whether at least one of the limits was tightened
  bool setLimitsToMax() override;
  // returns whether at least one of the limits was tightened
  bool setLimitsFromSimulation() override;

  void onLimitsUpdated() override;

private:
  Lib::vvector<unsigned> _simulationBalances;

  /*
   * LRS specific methods and fields for usage of limits
   */
public:
  bool ageLimited() const override;
  bool weightLimited() const override;

  bool fulfilsAgeLimit(Clause* cl) const override;
  // note: w here denotes the weight as returned by weight().
  // age is to be recovered from inference
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  bool fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override;
  bool fulfilsWeightLimit(Clause* cl) const override;
  // note: w here denotes the weight as returned by weight().
  // age is to be recovered from inference
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  bool fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override;
  bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const override;
  
}; // class PredicateSplitPassiveClauseContainer

class TheoryMultiSplitPassiveClauseContainer : public PredicateSplitPassiveClauseContainer
{
public:
  TheoryMultiSplitPassiveClauseContainer(bool isOutermost, const Shell::Options &opt, Lib::vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues);

private:
  float evaluateFeature(Clause* cl) const override;
  float evaluateFeatureEstimate(unsigned numPositiveLiterals, const Inference& inf) const override;
};

class AvatarMultiSplitPassiveClauseContainer : public PredicateSplitPassiveClauseContainer
{
public:
  AvatarMultiSplitPassiveClauseContainer(bool isOutermost, const Shell::Options &opt, Lib::vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues);

private:
  float evaluateFeature(Clause* cl) const override;
  float evaluateFeatureEstimate(unsigned numPositiveLiterals, const Inference& inf) const override;
};

class SineLevelMultiSplitPassiveClauseContainer : public PredicateSplitPassiveClauseContainer
{
public:
  SineLevelMultiSplitPassiveClauseContainer(bool isOutermost, const Shell::Options &opt, Lib::vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues);

private:
  float evaluateFeature(Clause* cl) const override;
  float evaluateFeatureEstimate(unsigned numPositiveLiterals, const Inference& inf) const override;
};

class PositiveLiteralMultiSplitPassiveClauseContainer : public PredicateSplitPassiveClauseContainer
{
public:
  PositiveLiteralMultiSplitPassiveClauseContainer(bool isOutermost, const Shell::Options &opt, Lib::vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues);

private:
  float evaluateFeature(Clause* cl) const override;
  float evaluateFeatureEstimate(unsigned numPositiveLiterals, const Inference& inf) const override;
};

};

#endif /* __PredicateSplitPassiveClauseContainer__ */
