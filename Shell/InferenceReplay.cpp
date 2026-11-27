/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Shell/InferenceReplay.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/Superposition.hpp"
#include "Kernel/Inference.hpp"
#include "Shell/InferenceRecorder.hpp"

#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Lib/Environment.hpp"
#include "Lib/ScopedLet.hpp"
#include "Lib/Stack.hpp"
#include "Saturation/Discount.hpp"

#include <unordered_set>
#include <type_traits>
#include <vector>

namespace Shell {
using namespace Kernel;
using namespace Inferences;

namespace {
/** Keep replay's index membership temporary, even when an engine throws.
 * Preserve the proof parents' search-time stores. Repeated parent
 * positions remain separate substitution banks but enter the index once. */
class ReplayContext {
public:
  explicit ReplayContext(Saturation::SaturationAlgorithm& alg)
    : _active(*alg.getActiveClauseContainer()) {}

  void activate(Clause* clause)
  {
    if (!_activated.insert(clause).second) { return; }
    _parents.push_back({clause, clause->store()});
    clause->setStore(Clause::ACTIVE);
    _active.add(clause);
  }

  ~ReplayContext()
  {
    for (auto [clause, store] : _parents) {
      _active.remove(clause);
      clause->setStore(store);
    }
  }

private:
  struct Parent { Clause* clause; Clause::Store store; };
  Saturation::ActiveClauseContainer& _active;
  std::unordered_set<Clause*> _activated;
  std::vector<Parent> _parents;
};

} // namespace

InferenceReplayer::InferenceReplayer() = default;
InferenceReplayer::~InferenceReplayer() = default;

void InferenceReplayer::makeInferenceEngine(OrderingSP ordering)
{
  ASS(!_alg);
  _problem = std::make_unique<Problem>();
  Lib::ScopedLet<bool> reconstruction(env.replayRecording, true);
  Lib::ScopedLet<OrderingSP> proofOrdering(InferenceStore::instance()->ordering,
                                         ordering);
  Ordering::unsetGlobalOrdering();
  _alg = std::make_unique<Saturation::Discount>(*_problem, *env.options);
  // Replay uses the proof ordering explicitly and releases the global cache.
  Ordering::unsetGlobalOrdering();
}

template<typename Engine>
void InferenceReplayer::runInference(const Unit& unit)
{
  constexpr bool isGenerating = std::is_base_of_v<GeneratingInferenceEngine, Engine>;
  Clause* premise = nullptr;
  ClauseStack context;
  for (const auto& parent : iterTraits(unit.getParents())) {
    if (!parent->isClause()) { return; }
    if (!premise) {
      premise = parent->asClause();
      if constexpr (!isGenerating) {
        continue;
      }
    }
    context.push(parent->asClause());
  }
  Lib::ScopedLet<bool> reconstruction(env.replayRecording, true);
  if (!premise) { return; }
  ASS(_alg);
  if constexpr (!isGenerating) {
    ASS_EQ(context.size(), 1);
  }
  Engine rule(*_alg);
  ReplayContext active(*_alg);
  for (Clause* clause : context) { active.activate(clause); }
  if constexpr (isGenerating) {
    runGenerating(rule, premise);
  } else {
    runForwardsSimp(rule, premise);
  }
}

const InferenceReplayInformation* InferenceReplayer::replayInference(Unit* goal)
{
  if (!goal->isClause()) { return nullptr; }
  InferenceRecorder recorder(goal->asClause());
  switch (goal->inference().rule()) {
  case InferenceRule::RESOLUTION:
  case InferenceRule::CONSTRAINED_RESOLUTION:
    runInference<BinaryResolution>(*goal); break;
  case InferenceRule::SUPERPOSITION:
  case InferenceRule::CONSTRAINED_SUPERPOSITION:
    if (env.higherOrder()) { runInference<Superposition<true>>(*goal); }
    else { runInference<Superposition<false>>(*goal); }
    break;
  case InferenceRule::FACTORING:
    runInference<Factoring>(*goal); break;
  case InferenceRule::FORWARD_DEMODULATION:
    if (env.higherOrder()) { runInference<ForwardDemodulation<true>>(*goal); }
    else { runInference<ForwardDemodulation<false>>(*goal); }
    break;
  default:
    break;
  }
  auto info = recorder.takeInformation();
  if (!info) { return nullptr; }
  auto result = info->replayInformation();
  ASS(result);
  env.proofExtra.replace(goal, std::move(info));
  return result;
}

void InferenceReplayer::runGenerating(GeneratingInferenceEngine& rule,
                                     Clause* premise)
{
  auto result = rule.generateSimplify(premise);
  while (result.clauses.hasNext()) { result.clauses.next(); }
}

void InferenceReplayer::runForwardsSimp(ForwardSimplificationEngine& rule,
                                      Clause* premise)
{
  Clause* replacement = nullptr;
  ClauseIterator premises;
  rule.perform(premise, replacement, premises);
}

} // namespace Shell
