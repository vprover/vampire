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
#include "Lib/Timer.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/ClauseQueue.hpp"
#include "Shell/Property.hpp"
#include "ClauseContainer.hpp"
#include "AbstractPassiveClauseContainers.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Metaiterators.hpp"

#include "Lib/Random.hpp"

// coming from z3/subsatsolver, resp., these are defined again inside torch
#undef DEFINE_TYPE
#undef LOG
#include <torch/script.h>

namespace Saturation {

using namespace Kernel;

class NeuralPassiveClauseContainer; // forward

class NeuralClauseEvaluationModel
{
private:
  torch::jit::script::Module _model;

  bool _computing = false;
  bool _recording = false;

  bool _useSimpleFeatures;
  bool _useProblemFeatures;
  bool _useGage;
  bool _useGweight;

  int64_t _gageEmbeddingSize;
  torch::Tensor _gageRuleEmbed;
  torch::jit::script::Module _gageCombine;
  torch::Tensor _gageProblemTweak;

  torch::Tensor _initialClauseGage;
  List<torch::Tensor>* _laterGageResults = nullptr; // just to prevent garbage collector from deleting too early
  unsigned _gageCurBaseLayer = 1;
  DHMap<unsigned,torch::Tensor> _gageEmbedStore;
  DHMap<unsigned,unsigned> _gageClLayers;
  Stack<Stack<std::tuple<Clause*,std::vector<int64_t>>>> _gageTodoLayers;

  int64_t _gweightEmbeddingSize;
  torch::jit::script::Module _gweightTermCombine;
  torch::Tensor _gweightStaticTweak;

  torch::Tensor _gweightSymbolEmbeds;
  List<torch::Tensor>* _gweightResults = nullptr; // just to prevent garbage collector from deleting too early
  unsigned _gweightCurBaseLayer = 1;
  DHMap<unsigned,torch::Tensor> _gweightTermEmbedStore;
  DHMap<unsigned,unsigned> _gweightTermLayers;
  Stack<Stack<std::tuple<int64_t,unsigned,float,std::vector<int64_t>>>> _gweightTodoLayers;

  Stack<Clause*> _gweightClauseTodo;
  DHMap<unsigned,torch::Tensor> _gweightClauseEmbeds;

  std::optional<torch::jit::Method> _evalClauses;
  std::optional<torch::jit::Method> _journal;

  unsigned _numFeatures;
  float _temp;

  std::function<bool(Clause*)> _makeReadyForEval;

  // this stored the computed logits + _temp * gumbel_noise
  DHMap<unsigned,float> _scores;
public:
  NeuralClauseEvaluationModel(const std::string clauseEvalModelFilePath, //  const std::string& tweak_str,
    std::function<bool(Clause*)> makeReadyForEval,
    uint64_t random_seed, unsigned num_cl_features, float temperature);

  void setRecording() {
    (*_model.find_method("set_recording"))({});
    _recording = true;
  }

  void setComputing() {
    (*_model.find_method("set_computing"))({});
    _computing = true;
  }

  void setStaticFeatures(unsigned num_prb_features, Problem& prb) {
    std::vector<float> probFeatures;
    probFeatures.reserve(num_prb_features);
    unsigned i = 0;
    Property::FeatureIterator it(prb.getProperty());
    while (i < num_prb_features && it.hasNext()) {
      probFeatures.push_back(it.next());
      i++;
    }

    (*_model.find_method("set_static_features"))({
      torch::from_blob(probFeatures.data(), {num_prb_features}, torch::TensorOptions().dtype(torch::kFloat32))
      });

    // get _gageProblemTweak from "gage_problem_tweak" field in the model
    _gageProblemTweak = _model.attr("gage_static_tweak").toTensor();
    _gweightStaticTweak = _model.attr("gweight_static_tweak").toTensor();
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
    (*_journal)({
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
      if (a > 0) {
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

  bool useProblemFeatures() {
    return _useProblemFeatures;
  }

  bool useSimpleFeatures() {
    return _useSimpleFeatures;
  }

  bool useGage() {
    return _useGage;
  }

  bool useGweight() {
    return _useGweight;
  }

  // no longer used under "fast"
  /*
  void embedPending() {
    (*_model.find_method("embed_pending"))({});
  }
  */

  int64_t gageEmbeddingSize() {
    return _gageEmbeddingSize;
  }

  int64_t gweightEmbeddingSize() {
    return _gweightEmbeddingSize;
  }

  const DHMap<unsigned,float>& getScores() { return _scores; }

  float evalClause(Clause* cl);

  template<typename T>
  void evalClauses(const T& clauses, bool justRecord = false) {
    int64_t sz = clauses.size() + _evalAlsoTheseInTheNextBulk->size();
    if (sz == 0) return;

    // std::cout << "ec for: " << std::endl;

    torch::NoGradGuard no_grad; // TODO: check if this is necessary here

    auto gageRect = (!justRecord && _useGage) ?
                    torch::empty({sz, _gageEmbeddingSize}, torch::TensorOptions().dtype(torch::kFloat32)) :
                    torch::empty(0, torch::TensorOptions().dtype(torch::kFloat32));
    auto gweightRect = (!justRecord && _useGweight) ?
                    torch::empty({sz, _gweightEmbeddingSize}, torch::TensorOptions().dtype(torch::kFloat32)) :
                    torch::empty(0, torch::TensorOptions().dtype(torch::kFloat32));

    std::vector<int64_t> clauseNums;
    std::vector<float> features(_numFeatures*sz);
    {
      int64_t j = 0;
      unsigned idx = 0;
      auto uIt = concatIters(clauses.iter(),_evalAlsoTheseInTheNextBulk->iter());
      while (uIt.hasNext()) {
        unsigned i = 0;
        Clause* cl = uIt.next();

        // std::cout << cl->number() << ", ";

        clauseNums.push_back((int64_t)cl->number());
        Clause::FeatureIterator cIt(cl);
        while (i++ < _numFeatures && cIt.hasNext()) {
          features[idx] = cIt.next();
          idx++;
        }

        if (_computing) { // could as well be (!justRecord) here
          if (_useGage)
            gageRect.index_put_({j}, _gageEmbedStore.get(cl->number()));
          if (_useGweight)
            gweightRect.index_put_({j}, _gweightClauseEmbeds.get(cl->number()));
        }
        j++;
      }
    }

    // std::cout << std::endl;

    auto result = (*_evalClauses)({
      std::move(clauseNums),
      torch::from_blob(features.data(), {sz,_numFeatures}, torch::TensorOptions().dtype(torch::kFloat32)),
      gageRect,
      gweightRect
    });

    if (justRecord) {
      return;
    }

    auto logits = result.toTensor();

    // cout << "Eval clauses for " << sz << " requires " << logits.requires_grad() << endl;

    {
      auto uIt = concatIters(clauses.iter(),_evalAlsoTheseInTheNextBulk->iter());
      unsigned idx = 0;
      while (uIt.hasNext()) {
        Clause* cl = uIt.next();
        float logit = logits[idx++].item().toDouble();
        if (_temp > 0.0) {
          // adding the gumbel noise
          logit += -_temp*log(-log(Random::getFloat(0.0,1.0)));
        }

        float* score;
        // only overwrite, if not present
        if (_scores.getValuePtr(cl->number(),score)) {
          *score = logit;
        }
      }
    }
  }

  /*
   * This will bulk-evaluate all the given clauses!
   * as well as (if non-null) the _evalAlsoTheseInTheNextBulk
   * clauses (as secretly agreed with the NeuralPassiveClauseContainer)
   */
  template<typename T>
  void bulkEval(const T& clauses) {
    TIME_TRACE(TimeTrace::DEEP_STUFF);

    Timer::updateInstructionCount(); // TODO: consider leaving this out (more efficient vampire, less precise stats)
    long long bulk_eval_start_instrs = Timer::elapsedInstructions();

    // std::cout << "bE:\n1:" << std::endl;

    {
      auto it = concatIters(clauses.iter(),_evalAlsoTheseInTheNextBulk->iter());
      while (it.hasNext()) {
        Clause* cl = it.next();
        // std::cout << cl->number() << ", ";
        _makeReadyForEval(cl);
      }
    }
    // std::cout << std::endl;

    gageEmbedPending();
    gweightEmbedPending();
    evalClauses(clauses);

    {
      auto it = _evalAlsoTheseInTheNextBulk->iter();
      while (it.hasNext()) {
        _delayedInsert(it.next());
      }
      _evalAlsoTheseInTheNextBulk->reset();
    }

    Timer::updateInstructionCount(); // TODO: consider leaving this out (more efficient vampire, less precise stats)
    env.statistics->bulkEvals += (Timer::elapsedInstructions()-bulk_eval_start_instrs);
  }

  // this is a low-effort version of evalClause (used, among other things, for delayedEvaluation deepire-style):
  // namely: if there is no value in the _scores map, it just returns a very optimistic constant
  float tryGetScore(Clause* cl);

private:
  // some friendship ugliness - just between NeuralClauseEvaluationModel and NeuralPassiveClauseContainer
  friend class NeuralPassiveClauseContainer;
  Stack<Clause*>* _evalAlsoTheseInTheNextBulk = new Stack<Clause*>(); // by default, a dummy empty stack
  std::function<void(Clause*)> _delayedInsert;
};

class NeuralScoreQueue
  : public ClauseQueue
{
public:
  NeuralScoreQueue(const DHMap<unsigned,float>& scores) : _scores(scores) {}

  typedef float OrdVal;
  static constexpr OrdVal maxOrdVal = std::numeric_limits<float>::max();
  OrdVal getOrdVal(Clause* cl) const {
    // it's responsibility of the surrounding container (here the NeuralPassiveClauseContainer)
    // to make sure clauses are evalauted in time for LRS estimations ...
    float val;
    if (_scores.find(cl->number(),val)) {
      return -val; // negating: NNs think large is good, queues think small is good
    }
    // .. if not, each such clause is considered "to be kept"
    return -maxOrdVal; // a very optimistic constant (since small is good)
  }
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


/**
 * A neural single queue solution to clause selection.
 */
class NeuralPassiveClauseContainer
: public SingleQueuePassiveClauseContainer<NeuralScoreQueue>
{
public:
  NeuralPassiveClauseContainer(bool isOutermost, const Shell::Options& opt,
    NeuralClauseEvaluationModel& model);

  bool isEmpty() const override { return _size == 0; }

  void add(Clause* cl) override;
  void remove(Clause* cl) override;
  Clause* popSelected() override;

private:
  NeuralClauseEvaluationModel& _model;
  Stack<Clause*> _delayedInsertionBuffer;

  unsigned _reshuffleAt;

  void delayedInsert(Clause* cl) { _queue.insert(cl); }
public:
  void simulationInit() override {
    _model.bulkEval(Stack<Clause*>());

    SingleQueuePassiveClauseContainer<NeuralScoreQueue>::simulationInit();
  }
};


};

#endif /* __NeuralPassiveClauseContainer__ */
