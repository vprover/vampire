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

/**
 * A class to be used by the neural experiments.
 *
 * Currently implemented without LRS support.
 *
 * In the long term, AWPassiveClauseContainer should be implementable
 * as a (binary) meta-container out of two SingleQueuePassiveClauseContainer(s)
 *
 **/
class BinaryMetaContainer : public PassiveClauseContainer
{
public:
  CLASS_NAME(BinaryMetaContainer);
  USE_ALLOCATOR(BinaryMetaContainer);

  BinaryMetaContainer(bool isOutermost, const Shell::Options& opt, vstring name,
      std::unique_ptr<PassiveClauseContainer> firstSubcontainer, std::unique_ptr<PassiveClauseContainer> secondSubcontainer, int firstRatio, int secondRatio)
      : PassiveClauseContainer(isOutermost, opt, name),
      _firstSubcontainer(std::move(firstSubcontainer)), _secondSubcontainer(std::move(secondSubcontainer)),
      _firstRatio(firstRatio), _secondRatio(secondRatio), _balance(0) { ASS_G(firstRatio,0); ASS_G(secondRatio,0); }

  virtual ~BinaryMetaContainer() {}

  void add(Clause* cl) override {
    CALL("BinaryMetaContainer::add");

    ASS(cl->store() == Clause::PASSIVE);

    _firstSubcontainer->add(cl);
    _secondSubcontainer->add(cl);

    if (_isOutermost)
    {
      addedEvent.fire(cl);
    }
  }

  void remove(Clause* cl) override {
    CALL("BinaryMetaContainer::remove");

    if (_isOutermost)
    {
      ASS(cl->store()==Clause::PASSIVE);
    }

    _firstSubcontainer->remove(cl);
    _secondSubcontainer->remove(cl);

    if (_isOutermost)
    {
      ASS(cl->store()==Clause::PASSIVE);
      removedEvent.fire(cl);
      ASS(cl->store() != Clause::PASSIVE);
    }
  }

  Clause* popSelected() override {
    CALL("BinaryMetaContainer::popSelected");

    bool selFromFirst;
    if (_balance > 0) {
      selFromFirst = true;
    } else if (_balance < 0) {
      selFromFirst = false;
    } else {
      selFromFirst = (_firstRatio <= _secondRatio);
    }

    Clause* cl;

    if (selFromFirst) {
      _balance -= _secondRatio;

      // cout << "Sel from first" << endl;

      cl = _firstSubcontainer->popSelected();
      _secondSubcontainer->remove(cl);
    } else {
      _balance += _firstRatio;

      // cout << "Sel from second" << endl;

      cl = _secondSubcontainer->popSelected();
      _firstSubcontainer->remove(cl);
    }

    if (_isOutermost) {
      selectedEvent.fire(cl);
    }

    return cl;
  }

  bool isEmpty() const override { return _firstSubcontainer->isEmpty() &&  _secondSubcontainer->isEmpty(); } // they should contain the same clauses, but whatever
  unsigned sizeEstimate() const override { return _firstSubcontainer->sizeEstimate(); }

private:
  std::unique_ptr<PassiveClauseContainer> _firstSubcontainer, _secondSubcontainer;
  int _firstRatio, _secondRatio; // these two are not really ratios, their form a ratio as a pair
  int _balance;

public:
  // brutally ignoring the LRS stuff
  void simulationInit() override {}
  bool simulationHasNext() override { return false; }
  void simulationPopSelected() override {}
  bool setLimitsToMax() override { return false; }
  bool setLimitsFromSimulation() override { return false; }
  void onLimitsUpdated() override {}

  bool ageLimited() const override { return false; }
  bool weightLimited() const override { return false; }
  bool fulfilsAgeLimit(Clause* c) const override { return true; }
  bool fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { return true; }
  bool fulfilsWeightLimit(Clause* cl) const override { return true; }
  bool fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { return true; }
  bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const override { return true; }
};


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

  void setDelayedEvaluator(void (*de)(Clause* cl)) {
    CALL("PredicateSplitPassiveClauseContainer::setDelayedEvaluator");

    ASS(_layeredArrangement); // currently only implemented for layered; does it even make sense for Tammet-style?
    _delayedEvaluator = de;
  }

private:
  void (*_delayedEvaluator)(Clause* cl);

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

class NeuralEvalSplitPassiveClauseContainer : public PredicateSplitPassiveClauseContainer
{
public:
  NeuralEvalSplitPassiveClauseContainer(bool isOutermost, const Shell::Options &opt, Lib::vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues);
private:
  float evaluateFeature(Clause* cl) const override;
  float evaluateFeatureEstimate(unsigned, const Inference& inf) const override;
};

};

#endif /* __PredicateSplitPassiveClauseContainer__ */
