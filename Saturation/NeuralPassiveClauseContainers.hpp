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
#include "Shell/Property.hpp"
#include "ClauseContainer.hpp"

#include "Lib/Allocator.hpp"

#include "Lib/Random.hpp"

// coming from z3/subsatsolver, resp., these are defined again inside torch
#undef DEFINE_TYPE
#undef LOG
#include <torch/script.h>

namespace Saturation {

using namespace Kernel;

class NeuralClauseEvaluationModel
{
private:
  torch::jit::script::Module _model;

  unsigned _numFeatures;
  float _temp;

  // this stored the computed logits + _temp * gumbel_noise
  DHMap<unsigned,float> _scores;
public:
  NeuralClauseEvaluationModel(const std::string clauseEvalModelFilePath, //  const std::string& tweak_str,
    uint64_t random_seed, unsigned num_cl_features, float temperature);

  void setRecording() {
    (*_model.find_method("set_recording"))(std::vector<torch::jit::IValue>());
  }

  void setComputing() {
    (*_model.find_method("set_computing"))(std::vector<torch::jit::IValue>());
  }

  void setProblemFeatures(unsigned num_prb_features, Problem& prb) {
    auto m = _model.find_method("set_problem_features");
    std::vector<torch::jit::IValue> inputs;
    std::vector<float> probFeatures;
    probFeatures.reserve(num_prb_features);
    unsigned i = 0;
    Property::FeatureIterator it(prb.getProperty());
    while (i < num_prb_features && it.hasNext()) {
      probFeatures.push_back(it.next());
      i++;
    }
    inputs.push_back(torch::from_blob(probFeatures.data(), {num_prb_features}, torch::TensorOptions().dtype(torch::kFloat32)));
    (*m)(std::move(inputs));
  }

  void gnnNodeKind(const char* node_name, const torch::Tensor& node_features) {
    auto m = _model.find_method("gnn_node_kind");
    std::vector<torch::jit::IValue> inputs;
    inputs.push_back(node_name);
    inputs.push_back(node_features);
    (*m)(std::move(inputs));
  }

  void gnnEdgeKind(const char* src_name,const char* tgt_name, std::vector<int64_t>& src_idxs, std::vector<int64_t>& tgt_idxs) {
    auto m = _model.find_method("gnn_edge_kind");
    std::vector<torch::jit::IValue> inputs;
    inputs.push_back(src_name);
    inputs.push_back(tgt_name);
    inputs.push_back(src_idxs);
    inputs.push_back(tgt_idxs);
    (*m)(std::move(inputs));
  }

  void gnnPerform(std::vector<int64_t>& clauseNums) {
    // the clause numbers in this vector are promised to go in the same order as the clausese in previously added gnnNodeKind("clause",...)
    auto m = _model.find_method("gnn_perform");
    std::vector<torch::jit::IValue> inputs;
    inputs.push_back(std::move(clauseNums));
    (*m)(std::move(inputs));
  }

  enum JournalEntry {
    JOURNAL_ADD = 0,
    JOURNAL_REM = 1,
    JOURNAL_SEL = 2,
  };

  void journal(JournalEntry tag, Clause* cl) {
    auto m = _model.find_method("journal_record");
    std::vector<torch::jit::IValue> inputs;
    inputs.push_back((int64_t)tag);
    inputs.push_back((int64_t)cl->number());
    (*m)(std::move(inputs));
  }

  void setProofUnitsAndSaveRecorded(std::vector<int64_t>& proof_units, const std::string& filename) {
    auto m = _model.find_method("set_proof_units_and_save_recorded");
    std::vector<torch::jit::IValue> inputs;
    inputs.push_back(std::move(proof_units));
    inputs.push_back(filename);
    (*m)(std::move(inputs));
  }

  void gageEnqueue(Clause* c, std::vector<int64_t>& parents) {
    auto m = _model.find_method("gage_enqueue");
    std::vector<torch::jit::IValue> inputs;
    inputs.push_back((int64_t)c->number());
    inputs.push_back((int64_t)toNumber(c->inference().rule()));
    inputs.push_back(std::move(parents));
    (*m)(std::move(inputs));
  }

  void gweightEnqueueTerm(int64_t id, unsigned functor, float sign, std::vector<int64_t>& args) {
    auto m = _model.find_method("gweight_enqueue_term");
    std::vector<torch::jit::IValue> inputs;
    inputs.push_back(id);
    inputs.push_back((int64_t)functor);
    inputs.push_back(sign);
    inputs.push_back(std::move(args));
    (*m)(std::move(inputs));
  }

  void gweightEnqueueClause(Clause* c, std::vector<int64_t>& lits) {
    auto m = _model.find_method("gweight_enqueue_clause");
    std::vector<torch::jit::IValue> inputs;
    inputs.push_back((int64_t)c->number());
    inputs.push_back(std::move(lits));
    (*m)(std::move(inputs));
  }

  void embedPending() {
    (*_model.find_method("embed_pending"))(std::vector<torch::jit::IValue>());
  }

  const DHMap<unsigned,float>& getScores() { return _scores; }

  float evalClause(Clause* cl);
  void evalClauses(Stack<Clause*>& clauses, bool justRecord = false);

  // this is a low-effort version of evalClause (used, among other things, for delayedEvaluation deepire-style):
  // namely: if there is no value in the _scores map, it just returns a very optimistic constant
  float tryGetScore(Clause* cl);
};

class ShuffledScoreQueue
  : public ClauseQueue
{
public:
  ShuffledScoreQueue(const DHMap<unsigned,float>& scores) : _scores(scores) {}
protected:
  virtual bool lessThan(Clause* c1,Clause* c2) {
    auto sc1 = _scores.get(c1->number());
    auto sc2 = _scores.get(c2->number());

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
  const DHMap<unsigned,float>& _scores;
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
  NeuralPassiveClauseContainer(bool isOutermost, const Shell::Options& opt,
    NeuralClauseEvaluationModel& model,
    std::function<void(Clause*)> makeReadyForEval);
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
  float _curLimit = _minLimit; // effectively no limit
  ScopedPtr<ClauseQueue::Iterator> _simulationIt;

  bool setLimits(float newLimit);
  bool exceedsLimit(Clause* cl) const {
    auto score = _model.tryGetScore(cl);
    // std::cout << "score "<<score << "  " << _curLimit << std::endl;
    return score < _curLimit;
  }
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

protected:
  void evalAndEnqueueDelayed();

private:
  NeuralClauseEvaluationModel& _model;
  ShuffledScoreQueue _queue;
  Stack<Clause*> _delayedInsertionBuffer;
  std::function<void(Clause*)> _makeReadyForEval;

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
  DHMap<unsigned,float> _scores;
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
