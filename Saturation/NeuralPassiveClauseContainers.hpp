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
 * @file NeuralPassiveClauseContainer.hpp
 * Defines the class NeuralPassiveClauseContainer and co.
 * @since 31/12/2007 Manchester
 */

#ifndef __NeuralPassiveClauseContainer__
#define __NeuralPassiveClauseContainer__

#include <memory>
#include <vector>
#include "Lib/Comparison.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/ClauseQueue.hpp"
#include "ClauseContainer.hpp"

#include "Lib/Allocator.hpp"

#include "Lib/Random.hpp"

// coming from z3/subsatsolver, resp., these are defined again inside torch
#undef DEFINE_TYPE
#undef LOG
#include <torch/script.h>

namespace Saturation {

using namespace Kernel;

static constexpr unsigned MAX_STAGES = 2; // basically, it's either 1 or 2 (at the moment)
typedef std::array<float,MAX_STAGES> Scores;

// Helper function to fill the array recursively
template<std::size_t... I>
constexpr std::array<float, sizeof...(I)> fillArrayImpl(float value, std::index_sequence<I...>) {
    // Use a fold expression or initializer list to fill the array with the constant value
    return {{ ((void)I, value)... }};
}

// Main function to generate the array
constexpr Scores constScores(float value) {
    return fillArrayImpl(value, std::make_index_sequence<MAX_STAGES>{});
}

class NeuralClauseEvaluationModel
{
private:
  torch::jit::script::Module _model;

  unsigned _numStages; // if < MAX_STAGES, the higher indices of Scores will remain ignored
  unsigned _numFeatures;
  float _temp;

  // this stored the computed logits + _temp * gumbel_noise
  DHMap<unsigned,Scores> _scores;
public:
  unsigned getNumStages() const { return _numStages; }

  NeuralClauseEvaluationModel(const std::string modelFilePath, const std::string& tweak_str,
    uint64_t random_seed, unsigned num_features, float temperature);

  const DHMap<unsigned,Scores>& getScoresMap() { return _scores; }

  Scores evalClause(Clause* cl);
  void evalClauses(UnprocessedClauseContainer& clauses);

  // this is a low-effort version of evalClause (used, among other things, for delayedEvaluation deepire-style):
  // namely: if there is no value in the _scores map, it just returns a very optimistic constant
  Scores tryGetScores(Clause* cl);
};

class ShuffledScoreQueue
  : public ClauseQueue
{
public:
  ShuffledScoreQueue() : _idx(0), _scoresMap(nullptr) {}

  void setScoresMap(const DHMap<unsigned,Scores>& map) { _scoresMap = &map; }
  void setIdx(unsigned i) { _idx = i; }
protected:
  virtual bool lessThan(Clause* c1,Clause* c2) {
    auto sc1 = _scoresMap->get(c1->number())[_idx];
    auto sc2 = _scoresMap->get(c2->number())[_idx];

    // reversing the order here: NNs think large is good, queues think small is good
    if (sc1 > sc2) {
      return true;
    }
    if (sc1 < sc2) {
      return false;
    }

    return c1->number() < c2->number();
  }
private:
  unsigned _idx;
  const DHMap<unsigned,Scores>* _scoresMap;
};

class LRSIgnoringPassiveClauseContainer
: public PassiveClauseContainer
{
public:
  LRSIgnoringPassiveClauseContainer(bool isOutermost, const Shell::Options& opt) : PassiveClauseContainer(isOutermost,opt) {}
  virtual ~LRSIgnoringPassiveClauseContainer() {}

  /*
   * LRS specific methods for computation of Limits
   */
public:
  void simulationInit() override { NOT_IMPLEMENTED; }
  bool simulationHasNext() override { return false; }
  void simulationPopSelected() override { NOT_IMPLEMENTED; }

  // returns whether at least one of the limits was tightened
  bool setLimitsToMax() override { return false; }
  // returns whether at least one of the limits was tightened
  bool setLimitsFromSimulation() override { return false; }

  void onLimitsUpdated() override { NOT_IMPLEMENTED; }

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

/**
 * A neural single queue solution to clause selection.
 */
class NeuralPassiveClauseContainer
: public LRSIgnoringPassiveClauseContainer
{
public:
  NeuralPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, NeuralClauseEvaluationModel& model);
  virtual ~NeuralPassiveClauseContainer(){}

  unsigned sizeEstimate() const override { return _size; }
  bool isEmpty() const override { return _size == 0; }
  void add(Clause* cl) override;
  void remove(Clause* cl) override;

  Clause* popSelected() override;

  /*
   * LRS specific methods for computation of Limits
   */
private:
  // we use min, because scores and salts are compared inverted (not as e.g. age and weigth)
  static constexpr float _minLimit = -std::numeric_limits<float>::max();
  unsigned _limitedAtStage = 0;
  float _curLimit = _minLimit; // effectively no limit

  bool setLimits(float newLimit, unsigned newStage);
  bool exceedsLimit(Clause* cl) const {
    auto scores = _model.tryGetScores(cl);
    return scores[_limitedAtStage] < _curLimit;
  }

  ScopedPtr<ClauseQueue::Iterator> _simulationIt;
  unsigned _simulationStage;
  unsigned _simulationSelectionsSoFar;

public:
  void simulationInit() override;
  bool simulationHasNext() override;
  void simulationPopSelected() override;

  // returns whether at least one of the limits was tightened
  bool setLimitsToMax() override { _curLimit = _minLimit; return false; }
  // returns whether at least one of the limits was tightened
  bool setLimitsFromSimulation() override;
  void onLimitsUpdated() override;

  /*
   * LRS specific methods and fields for usage of limits
   */
  bool ageLimited() const override { return _curLimit != _minLimit; }
  bool weightLimited() const override { return _curLimit != _minLimit; }

  bool fulfilsAgeLimit(Clause* cl) const override { return !exceedsLimit(cl); }
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.

  bool fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { return true; }
  bool fulfilsWeightLimit(Clause* cl) const override { return !exceedsLimit(cl); }
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  bool fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { return true; }

  bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const override { return true; }

private:
  NeuralClauseEvaluationModel& _model;

  unsigned _numStages;
  DArray<ShuffledScoreQueue> _queues;

  unsigned _curStage;

  unsigned _selectionsSoFar;
  unsigned _nextRestageAt;

  unsigned _size;
  unsigned _reshuffleAt;
};

class LearnedPassiveClauseContainer
: public LRSIgnoringPassiveClauseContainer
{
protected:
  virtual float scoreClause(Clause*) = 0;
public:
  LearnedPassiveClauseContainer(bool isOutermost, const Shell::Options& opt);
  virtual ~LearnedPassiveClauseContainer() {}

  unsigned sizeEstimate() const override { return _size; }
  bool isEmpty() const override { return _size == 0; }

  void add(Clause* cl) override;
  void remove(Clause* cl) override;
  Clause* popSelected() override;
private:
  DHMap<unsigned,Scores> _scores;
  ShuffledScoreQueue _queue;
  unsigned _size;
  float _temperature;
};

class LearnedPassiveClauseContainerExperNF12cLoop5
: public LearnedPassiveClauseContainer
{
public:
  LearnedPassiveClauseContainerExperNF12cLoop5(bool isOutermost, const Shell::Options& opt) :
    LearnedPassiveClauseContainer(isOutermost,opt) {}
  ~LearnedPassiveClauseContainerExperNF12cLoop5() override {}
protected:
  float scoreClause(Clause*) override;
};

};

#endif /* __NeuralPassiveClauseContainer__ */
