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
 * @file NeuralPassiveClauseContainer.cpp
 * Implements class NeuralPassiveClauseContainer and co.
 * @since 30/12/2007 Manchester
 */

#define USING_LIBTORCH // see Lib/Output.hpp

#include <cmath>
#include <climits>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Random.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/SoftmaxClauseQueue.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"

#include "SaturationAlgorithm.hpp"
#include "Splitter.hpp"

#if VDEBUG
#include <iostream>
#endif

#include "NeuralPassiveClauseContainers.hpp"

#define DEBUG_MODEL 0
#include <torch/utils.h>

namespace Saturation
{
using namespace std;
using namespace Lib;
using namespace Kernel;

NeuralClauseEvaluationModel::NeuralClauseEvaluationModel(const std::string clauseEvalModelFilePath,
  std::function<bool(Clause*)> makeReadyForEval,
  // const std::string& tweak_str,
  uint64_t random_seed, unsigned num_cl_features, float temperature) :
  _numFeatures(num_cl_features), _temp(temperature), _makeReadyForEval(makeReadyForEval)
{
  TIME_TRACE("neural model warmup");

  Timer::updateInstructionCount();
  long long neural_model_start_instrs = Timer::elapsedInstructions();

#if DEBUG_MODEL
  auto start = env.timer->elapsedMilliseconds();
#endif

  // seems to be making this nicely single-threaded
  at::set_num_threads(1);
  at::set_num_interop_threads(1);

  torch::manual_seed(random_seed);

  _model = torch::jit::load(clauseEvalModelFilePath);
  _model.eval();

  /*
  if (!tweak_str.empty()) {
    if (auto m = _model.find_method("eatMyTweaks")) { // if the model is not interested in tweaks, it will get none!
      std::vector<float> tweaks;

      std::size_t i=0,j;
      while (true) {
        j = tweak_str.find_first_of(',',i);

        auto t = tweak_str.substr(i,j-i);
        if (t.empty()) {
          break;
        }

        float nextVal;
        ALWAYS(Int::stringToFloat(t.c_str(),nextVal));
        tweaks.push_back(nextVal);

        if (j == std::string::npos) {
          break;
        }

        i = j+1;
      }

      std::vector<torch::jit::IValue> inputs;
      inputs.push_back(torch::jit::IValue(torch::from_blob(tweaks.data(), {static_cast<long long>(tweaks.size())}, torch::TensorOptions().dtype(torch::kFloat32))));
      (*m)(std::move(inputs));
    }
  }
  */

#if DEBUG_MODEL
  cout << "Model loaded in " << env.timer->elapsedMilliseconds() - start << " ms" << endl;
  cout << at::get_parallel_info() << endl;
#endif

  _useSimpleFeatures = (*_model.find_method("use_simple_features"))({}).toBool();
  if (!_useSimpleFeatures) {
    _numFeatures = 0;
  }
  _useProblemFeatures = (*_model.find_method("use_problem_features"))({}).toBool();
  _useGage = (*_model.find_method("use_gage"))({}).toBool();
  _useGweight = (*_model.find_method("use_gweight"))({}).toBool();

  _gageEmbeddingSize = (*_model.find_method("gage_embedding_size"))({}).toInt();
  _gageRuleEmbed = _model.attr("gage_rule_embed").toModule().attr("weight").toTensor();
  _gageCombine = _model.attr("gage_combine").toModule();

  _gweightEmbeddingSize = (*_model.find_method("gweight_embedding_size"))({}).toInt();
  auto _gweightVarEmbed = _model.attr("gweight_var_embed").toModule().forward({torch::Tensor()}).toTensor();
  _gweightTermEmbedStore.insert(0,_gweightVarEmbed);

  _gweightTermCombine = _model.attr("gweight_term_combine").toModule();

  _evalClauses = _model.find_method("eval_clauses");
  _journal = _model.find_method("journal_record");

  /*
  cout << _model.attr("tweaks").toModule().attr("0") << endl;

  auto param_list = _model.attr("tweaks").toModule();
  auto his_type = param_list.type();
  for (size_t i = 0; i < his_type->numAttributes(); i++) {
    cout << his_type->getAttributeName(i) << endl;
  }
  */

  Timer::updateInstructionCount();
  env.statistics->neuralModelWarmup += (Timer::elapsedInstructions()-neural_model_start_instrs);
}

float NeuralClauseEvaluationModel::tryGetScore(Clause* cl) {
  float* someVal = _scores.findPtr(cl->number());
  if (someVal) {
    return *someVal;
  }
  // a very optimistic constant (since large is good)
  return std::numeric_limits<float>::max();
}

// obsolete - to revive, if we were to compare to ENIGMA-style (classifier) approach to lawa
float NeuralClauseEvaluationModel::evalClause(Clause* cl) {
  float* someVal = _scores.findPtr(cl->number());
  if (someVal) {
    return *someVal;
  }

  float logit;
  {
    TIME_TRACE("neural model evaluation");

    std::vector<torch::jit::IValue> inputs;

    std::vector<float> features(_numFeatures);
    unsigned i = 0;
    Clause::FeatureIterator it(cl);
    while (i < _numFeatures && it.hasNext()) {
      features[i] = it.next();
      i++;
    }
    ASS_EQ(features.size(),_numFeatures);
    inputs.push_back(torch::from_blob(features.data(), {_numFeatures}, torch::TensorOptions().dtype(torch::kFloat32)));

    logit = _model.forward(std::move(inputs)).toTensor().item().toDouble();
  }

  if (_temp > 0.0) {
    // adding the gumbel noise
    logit += -_temp*log(-log(Random::getFloat(0.0,1.0)));
  }

  // cout << "New clause has " << res << " with number " << cl->number() << endl;
  _scores.insert(cl->number(),logit);
  return logit;
}

void NeuralClauseEvaluationModel::gageEmbedPending()
{
  torch::NoGradGuard no_grad; // TODO: check if this is necessary here
  /*
  for todos in self.gage_todo_layers:
    ruleIdxs: list[int] = [] # into gage_rule_embed
    mainPrems = []
    otherPrems = []
    for clNum,infRule,parents in todos:
      ruleIdxs.append(infRule)
      mainPrems.append(self.gage_embed_store[parents[0]])
      if len(parents) == 1:
        otherPrems.append(torch.zeros(HP.GAGE_EMBEDDING_SIZE))
      elif len(parents) == 2:
        otherPrems.append(self.gage_embed_store[parents[1]])
      else:
        # this would work even in the binary case, but let's not invoke the monster if we don't need to
        otherPrem = torch.sum(torch.stack([self.gage_embed_store[parents[p]] for p in parents[1:]]),dim=0)/(len(parents)-1)
        otherPrems.append(otherPrem)
    ruleEbeds = self.gage_rule_embed(torch.tensor(ruleIdxs))
    mainPremEbeds = torch.stack(mainPrems)
    otherPremEbeds = torch.stack(otherPrems)
  */
  for (int64_t i = 0; i < static_cast<int64_t>(_gageTodoLayers.size()); i++) {
    Stack<std::tuple<Clause*,std::vector<int64_t>>>& todos = _gageTodoLayers[i];
    auto rect = torch::empty({static_cast<int64_t>(todos.size()), 3*_gageEmbeddingSize}, torch::TensorOptions().dtype(torch::kFloat32));
    {
      auto it = todos.iterFifo();
      int64_t j = 0;
      while (it.hasNext()) {
        const auto& [c,parents] = it.next();
        auto ruleIdx = (int64_t)toNumber(c->inference().rule());
        rect.index_put_({j, torch::indexing::Slice(0, _gageEmbeddingSize)}, _gageRuleEmbed.index({ruleIdx}));
        rect.index_put_({j, torch::indexing::Slice(1*_gageEmbeddingSize, 2*_gageEmbeddingSize)},
                (parents.size() == 0) ? torch::zeros({_gageEmbeddingSize}) : _gageEmbedStore.get(parents[0]));
        int64_t k = 1;
        auto remainingPremisesEmbedSum = torch::zeros({_gageEmbeddingSize});
        while (k < parents.size()) {
          remainingPremisesEmbedSum += _gageEmbedStore.get(parents[k++]);
        }
        k--; // now it reflects the number of parents actually summed up in remainingPremisesEmbedSum
        if (k > 1) {
          rect.index_put_({j, torch::indexing::Slice(2*_gageEmbeddingSize, 3*_gageEmbeddingSize)}, remainingPremisesEmbedSum/k);
        } else {
          rect.index_put_({j, torch::indexing::Slice(2*_gageEmbeddingSize, 3*_gageEmbeddingSize)}, remainingPremisesEmbedSum);
        }

        j++;
      }
    }
    /*
      res = self.gage_combine(torch.cat((ruleEbeds, mainPremEbeds, otherPremEbeds), dim=1))
      for j,(clNum,_,_) in enumerate(todos):
        self.gage_embed_store[clNum] = res[j]
    */
    auto res = _gageCombine.forward({rect}).toTensor();
    // adding the tweak to each column in res
    res += _gageStaticTweak;
    {
      auto it = todos.iterFifo();
      int64_t j = 0;
      while (it.hasNext()) {
        _gageEmbedStore.insert(std::get<0>(it.next())->number(),res.index({j}));
        j++;
      }
    }
    List<torch::Tensor>::push(res, _laterGageResults); // just to prevent garbage collector from deleting too early
  }
  /*
    self.gage_cur_base_layer += len(self.gage_todo_layers)
    empty_todo_layers: list[list[Tuple[int,int,list[int]]]] = []
    self.gage_todo_layers = empty_todo_layers
  */
  _gageCurBaseLayer += _gageTodoLayers.size();
  _gageTodoLayers.reset();
}

void NeuralClauseEvaluationModel::gweightEmbedPending() {
  torch::NoGradGuard no_grad; // TODO: check if this is necessary here

  /*
  # first like what gage does with clause, but here with terms
  for todos in self.gweight_todo_layers:
    functors = []
    signs = []
    first_args = []
    other_args = []
    for id,functor,sign,args in todos:
      functors.append(self.gweight_symbol_embeds[functor])
      signs.append(torch.tensor([sign]))
      if len(args) == 0:
        first_args.append(torch.zeros(HP.GWEIGHT_EMBEDDING_SIZE))
        other_args.append(torch.zeros(HP.GWEIGHT_EMBEDDING_SIZE))
      else:
        first_args.append(self.get_subterm_embed(args[0]))
        if len(args) == 1:
          other_args.append(torch.zeros(HP.GWEIGHT_EMBEDDING_SIZE))
        else:
          other_arg = torch.sum(torch.stack([self.get_subterm_embed(a) for a in args[1:]]),dim=0)/(len(args)-1)
          other_args.append(other_arg)
  */
  for (int64_t i = 0; i < static_cast<int64_t>(_gweightTodoLayers.size()); i++) {
    Stack<std::tuple<int64_t,unsigned,float,std::vector<int64_t>>>& todos = _gweightTodoLayers[i];
    auto rect = torch::empty({static_cast<int64_t>(todos.size()), 1+3*_gweightEmbeddingSize}, torch::TensorOptions().dtype(torch::kFloat32));

    auto it = todos.iterFifo();
    int64_t j = 0;
    while (it.hasNext()) {
      const auto& [id,functor,sign,args] = it.next();
      rect.index_put_({j, torch::indexing::Slice(0, _gweightEmbeddingSize)}, _gweightSymbolEmbeds.index({(int64_t)functor}));
      rect.index_put_({j, _gweightEmbeddingSize}, sign);
      if (args.size() == 0) {
        rect.index_put_({j, torch::indexing::Slice(1+_gweightEmbeddingSize, 1+3*_gweightEmbeddingSize)}, torch::zeros({2*_gweightEmbeddingSize}));
      } else {
        rect.index_put_({j, torch::indexing::Slice(1+_gweightEmbeddingSize, 1+2*_gweightEmbeddingSize)}, _gweightTermEmbedStore.get(args[0]));
        int64_t k = 1;
        auto remainingArgsEmbedSum = torch::zeros({_gweightEmbeddingSize});
        while (k < args.size()) {
          remainingArgsEmbedSum += _gweightTermEmbedStore.get(args[k++]);
        }
        k--; // now it reflects the number of args actually summed up in remainingArgsEmbedSum
        if (k > 1) {
          rect.index_put_({j, torch::indexing::Slice(1+2*_gweightEmbeddingSize, 1+3*_gweightEmbeddingSize)}, remainingArgsEmbedSum/k);
        } else {
          rect.index_put_({j, torch::indexing::Slice(1+2*_gweightEmbeddingSize, 1+3*_gweightEmbeddingSize)}, remainingArgsEmbedSum);
        }
      }
      j++;
    }
    /*
      res = self.gweight_term_combine(torch.cat((torch.stack(functors), torch.stack(signs), torch.stack(first_args), torch.stack(other_args)), dim=1))
      for j,(id,_,_,_) in enumerate(todos):
      self.gweight_term_embed_store[id] = res[j]
    */
    auto res = _gweightTermCombine.forward({rect}).toTensor();
    res += _gweightStaticTweak;
    {
      auto it = todos.iterFifo();
      int64_t j = 0;
      while (it.hasNext()) {
        _gweightTermEmbedStore.insert(std::get<0>(it.next()),res.index({j}));
        j++;
      }
    }
    List<torch::Tensor>::push(res, _gweightResults); // just to prevent garbage collector from deleting too early
  }
  /*
    self.gweight_cur_base_layer += len(self.gweight_todo_layers)
    empty_todo_layers: list[list[Tuple[int,int,float,list[int]]]] = []
    self.gweight_todo_layers = empty_todo_layers
  */
  _gweightCurBaseLayer += _gweightTodoLayers.size();
  _gweightTodoLayers.reset();

  /*
    # second, do the clauses part
    for j,(cl_num,lits) in enumerate(self.gweight_clause_todo):
      lit_embeds = torch.stack([self.gweight_term_embed_store[lit] for lit in lits])
      # TODO: try: avg over lits, max over lits, attention over lits, extra non-linearity level, ...
      self.gweight_clause_embeds[cl_num] = torch.sum(lit_embeds,dim=0)
    empty_clause_todo: List[Tuple[int, List[int]]] = []
    self.gweight_clause_todo = empty_clause_todo
  */
  {
    auto it = _gweightClauseTodo.iterFifo();
    while (it.hasNext()) {
      Clause* c = it.next();
      auto clauseEmbed = torch::zeros(_gweightEmbeddingSize);
      for (Literal* lit : c->iterLits()) {
        // using negative indices for literals (otherwise might overlap with term ids!)
        int64_t litId = -1-(int64_t)lit->getId(); // an ugly copy-paste from SaturationAlgorithm.cpp
        clauseEmbed += _gweightTermEmbedStore.get(litId);
      }
      _gweightClauseEmbeds.insert(c->number(),clauseEmbed);
    }
    _gweightClauseTodo.reset();
  }
}

NeuralPassiveClauseContainer::NeuralPassiveClauseContainer(bool isOutermost, const Shell::Options& opt,
  NeuralClauseEvaluationModel& model)
  : SingleQueuePassiveClauseContainer<NeuralScoreQueue>(isOutermost,opt,model.getScores()),
  _model(model), _reshuffleAt(opt.reshuffleAt())
{
  ASS(_isOutermost);

  delete _model._evalAlsoTheseInTheNextBulk; // delete the default one
  _model._evalAlsoTheseInTheNextBulk = &_delayedInsertionBuffer;

  _model._delayedInsert = std::bind(&NeuralPassiveClauseContainer::delayedInsert, this, std::placeholders::_1);
}

void NeuralPassiveClauseContainer::add(Clause* cl)
{
  float dummy;
  if (_model.getScores().find(cl->number(),dummy)) {
    _queue.insert(cl);
  } else {
    _delayedInsertionBuffer.push(cl);
  }

  // cout << "Inserting " << cl->number() << endl;
  _size++;

  ASS(cl->store() == Clause::PASSIVE);
  addedEvent.fire(cl);
}

void NeuralPassiveClauseContainer::remove(Clause* cl)
{
  ASS(cl->store()==Clause::PASSIVE);

  // cout << "Removing " << cl->number() << endl;
  if (!_delayedInsertionBuffer.remove(cl)) {
    _queue.remove(cl);
  }
  _size--;

  removedEvent.fire(cl);
  ASS(cl->store()!=Clause::PASSIVE);
}

Clause* NeuralPassiveClauseContainer::popSelected()
{
  ASS(_size);

  _model.bulkEval(Stack<Clause*>());

  static unsigned popCount = 0;
  if (++popCount == _reshuffleAt) {
    // cout << "reshuffled at "<< popCount << endl;
    Random::resetSeed();
  }

  // cout << "About to pop" << endl;
  Clause* cl = _queue.pop();
  // cout << "Got " << cl->number() << endl;
  // cout << "popped from " << _size << " got " << cl->toString() << endl;
  _size--;

  if (popCount == _reshuffleAt) {
    cout << "s: " << cl->number() << '\n';
  }

  selectedEvent.fire(cl);
  return cl;
}


} // namespace Saturation
