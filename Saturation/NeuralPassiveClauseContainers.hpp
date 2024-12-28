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

  bool _computing = false;
  bool _recording = false;

  bool _useSimpleFeatures;

  int64_t _gageEmbeddingSize;
  torch::Tensor _gageRuleEmbed;
  torch::jit::script::Module _gageCombine;

  torch::Tensor _initialClauseGage;
  List<torch::Tensor>* _laterGageResults = nullptr; // just to prevent garbage collector from deleting too early
  unsigned _gageCurBaseLayer = 1;
  DHMap<unsigned,torch::Tensor> _gageEmbedStore;
  DHMap<unsigned,unsigned> _gageClLayers;
  Stack<Stack<std::tuple<Clause*,std::vector<int64_t>>>> _gageTodoLayers;

  torch::Tensor getSubtermEmbed(int64_t id);

  int64_t _gweightEmbeddingSize;
  torch::Tensor _gweightVarEmbed;
  torch::jit::script::Module _gweightTermCombine;

  torch::Tensor _gweightSymbolEmbeds;
  List<torch::Tensor>* _gweightResults = nullptr; // just to prevent garbage collector from deleting too early
  unsigned _gweightCurBaseLayer = 1;
  DHMap<unsigned,torch::Tensor> _gweightTermEmbedStore;
  DHMap<unsigned,unsigned> _gweightTermLayers;
  Stack<Stack<std::tuple<int64_t,unsigned,float,std::vector<int64_t>>>> _gweightTodoLayers;

  Stack<Clause*> _gweightClauseTodo;
  DHMap<unsigned,torch::Tensor> _gweightClauseEmbeds;

  std::optional<torch::jit::Method> _evalClauses;

  unsigned _numFeatures;
  float _temp;

  // this stored the computed logits + _temp * gumbel_noise
  DHMap<unsigned,float> _scores;
public:
  NeuralClauseEvaluationModel(const std::string clauseEvalModelFilePath, //  const std::string& tweak_str,
    uint64_t random_seed, unsigned num_cl_features, float temperature);

  void setRecording() {
    (*_model.find_method("set_recording"))({});
    _recording = true;
  }

  void setComputing() {
    (*_model.find_method("set_computing"))({});
    _computing = true;
  }

  void setProblemFeatures(unsigned num_prb_features, Problem& prb) {
    std::vector<float> probFeatures;
    probFeatures.reserve(num_prb_features);
    unsigned i = 0;
    Property::FeatureIterator it(prb.getProperty());
    while (i < num_prb_features && it.hasNext()) {
      probFeatures.push_back(it.next());
      i++;
    }

    (*_model.find_method("set_problem_features"))({
      torch::from_blob(probFeatures.data(), {num_prb_features}, torch::TensorOptions().dtype(torch::kFloat32))
      });
  }

  void gnnNodeKind(const char* node_name, const torch::Tensor& node_features) {
    (*_model.find_method("gnn_node_kind"))({
      node_name,node_features
      });
  }

  void gnnEdgeKind(const char* src_name,const char* tgt_name, std::vector<int64_t>& src_idxs, std::vector<int64_t>& tgt_idxs) {
    (*_model.find_method("gnn_edge_kind"))({
      src_name,tgt_name,src_idxs,tgt_idxs
      });
  }

  void gnnPerform(std::vector<int64_t>& clauseNums) {
    // the clause numbers in this vector are promised to go in the same order as the clausese in previously added gnnNodeKind("clause",...)
     auto res = (*_model.find_method("gnn_perform"))({
      clauseNums
      });

    if (_computing) {
      auto tup = res.toTuple();
      _initialClauseGage = tup->elements()[0].toTensor();
      _gweightSymbolEmbeds = tup->elements()[1].toTensor();

      for (unsigned i = 0; i < clauseNums.size(); i++) {
        _gageEmbedStore.insert(clauseNums[i],_initialClauseGage[i]);
        _gageClLayers.insert(clauseNums[i],0);
      }
    }
  }

  enum JournalEntry {
    JOURNAL_ADD = 0,
    JOURNAL_REM = 1,
    JOURNAL_SEL = 2,
  };

  void journal(JournalEntry tag, Clause* cl) {
    auto m = _model.find_method("journal_record");
    (*m)({
      (int64_t)tag,
      (int64_t)cl->number()
      });
  }

  void setProofUnitsAndSaveRecorded(std::vector<int64_t>& proof_units, const std::string& filename) {
    (*_model.find_method("set_proof_units_and_save_recorded"))({
      std::move(proof_units),
      filename
    });
  }

  void gageEnqueueOne(Clause* c, std::vector<int64_t>& parents) {
    /*
      layer_idx = max(1+max(self.gage_cl_layers[p] for p in parents),self.gage_cur_base_layer)
      # index (counting from 0 with the initials) where cl_num could (and will) be derived
      self.gage_cl_layers[cl_num] = layer_idx

      eff_layer_idx = layer_idx-self.gage_cur_base_layer
      if len(self.gage_todo_layers) == eff_layer_idx:
        empty_todo_layer: list[Tuple[int,int,list[int]]] = []
        self.gage_todo_layers.append(empty_todo_layer)
      self.gage_todo_layers[eff_layer_idx].append((cl_num,inf_rule,parents))
    */
    unsigned layer_idx = 0;
    for (auto p : parents) {
      layer_idx = std::max(layer_idx,_gageClLayers.get(p));
    }
    layer_idx++;
    layer_idx = std::max(layer_idx,_gageCurBaseLayer);
    _gageClLayers.insert(c->number(),layer_idx);

    unsigned eff_layer_idx = layer_idx-_gageCurBaseLayer;
    if (_gageTodoLayers.size() == eff_layer_idx) {
      _gageTodoLayers.push(Stack<std::tuple<Clause*,std::vector<int64_t>>>());
    }
    _gageTodoLayers[eff_layer_idx].push(make_tuple(c, parents));
  }

  void gageEnqueue(Clause* c, std::vector<int64_t>& parents) {
    if (_computing) {
      gageEnqueueOne(c,parents);
    }

    if (_recording) {
      (*_model.find_method("gage_enqueue"))({
        (int64_t)c->number(),
        (int64_t)toNumber(c->inference().rule()),
        std::move(parents)
        });
    }
  }

  void gageEmbedPending();

  /*
    def gweight_enqueue_one_term(self,id: int, functor: int, sign: float, args: list[int]):
    if args:
      # layer_idx = 1+max(self.gweight_term_layers[a] for a in args if a >= 0)
      layer_idx = 0
      for a in args:
        if a >= 0:
          v = self.gweight_term_layers[a]
          if v > layer_idx:
            layer_idx = v
      layer_idx += 1
    else:
      layer_idx = 0
    layer_idx = max(layer_idx,self.gweight_cur_base_layer)

    self.gweight_term_layers[id] = layer_idx

    eff_layer_idx = layer_idx-self.gweight_cur_base_layer
    if len(self.gweight_todo_layers) == eff_layer_idx:
      empty_todo_layer: list[Tuple[int,int,float,list[int]]] = []
      self.gweight_todo_layers.append(empty_todo_layer)
    self.gweight_todo_layers[eff_layer_idx].append((id,functor,sign,args))
  */
  void gweightEnqueuOneTerm(int64_t id, unsigned functor, float sign, std::vector<int64_t>& args) {
    unsigned layer_idx = 0;
    for (auto a : args) {
      if (a >= 0) {
        layer_idx = std::max(layer_idx,_gweightTermLayers.get(a));
      }
    }
    layer_idx++;
    layer_idx = std::max(layer_idx,_gweightCurBaseLayer);
    _gweightTermLayers.insert(id,layer_idx);

    unsigned eff_layer_idx = layer_idx-_gweightCurBaseLayer;
    if (_gweightTodoLayers.size() == eff_layer_idx) {
      _gweightTodoLayers.push(Stack<std::tuple<int64_t,unsigned,float,std::vector<int64_t>>>());
    }
    _gweightTodoLayers[eff_layer_idx].push(std::make_tuple(id,functor,sign,args));
  }

  void gweightEnqueueTerm(int64_t id, unsigned functor, float sign, std::vector<int64_t>& args) {
    if (_computing) {
      gweightEnqueuOneTerm(id,functor,sign,args);
    }

    if (_recording) {
      (*_model.find_method("gweight_enqueue_term"))({
        id,
        (int64_t)functor,
        sign,
        std::move(args)
        });
    }
  }

  void gweightEmbedPending();

  void gweightEnqueueClause(Clause* c, std::vector<int64_t>& lits) {
    if (_computing) {
      _gweightClauseTodo.push(c);
    }

    if (_recording) {
      (*_model.find_method("gweight_enqueue_clause"))({
        (int64_t)c->number(),
        std::move(lits)
        });
    }
  }

  void printStats() {
    std::cout << "gage_stat: " << (*_model.find_method("gage_stat"))({}) << std::endl;
    std::cout << "gweight_stat: " << (*_model.find_method("gweight_stat"))({}) << std::endl;
  }

  bool useProblemFeatures() {
    return (*_model.find_method("use_problem_features"))({}).toBool();
  }

  bool useSimpleFeatures() {
    return (*_model.find_method("use_simple_features"))({}).toBool();
  }

  bool useGage() {
    return (*_model.find_method("use_gage"))({}).toBool();
  }

  bool useGweight() {
    return (*_model.find_method("use_gweight"))({}).toBool();
  }

  void embedPending() {
    (*_model.find_method("embed_pending"))({});
  }

  int64_t gageEmbeddingSize() {
    return (*_model.find_method("gage_embedding_size"))({}).toInt();
  }

  int64_t gweightEmbeddingSize() {
    return (*_model.find_method("gweight_embedding_size"))({}).toInt();
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
