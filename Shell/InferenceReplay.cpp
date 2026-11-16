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
#include "Saturation/Discount.hpp"

#include <unordered_set>
#include <vector>

namespace Shell {
using namespace Kernel;
using namespace Inferences;

namespace {
/** Keep replay's index membership temporary, even when an engine throws.
 * Preserve the proof parents' search-time stores and ages. Repeated parent
 * positions remain separate substitution banks but enter the index once. */
class ReplayContext {
public:
  explicit ReplayContext(Saturation::SaturationAlgorithm& alg)
    : _active(*alg.getActiveClauseContainer()) {}

  void activate(Clause* clause, bool resetAge = false)
  {
    if (!_activated.insert(clause).second) { return; }
    _parents.push_back({clause, clause->store(), clause->age()});
    // Index removal can release a clause. Hold it until its store is restored.
    clause->incRefCnt();
    clause->setStore(Clause::ACTIVE);
    if (resetAge) { clause->setAge(0); }
    _active.add(clause);
  }

  ~ReplayContext()
  {
    for (auto [clause, store, age] : _parents) {
      _active.remove(clause);
      clause->setAge(age);
      clause->setStore(store);
      clause->decRefCnt();
    }
  }

private:
  struct Parent { Clause* clause; Clause::Store store; unsigned age; };
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
  Lib::ScopedLet<bool> reconstruction(env.reconstruction, true);
  // Each replay constructs its own rule. Only DISCOUNT's active container and
  // indexes are needed; installing all search engines would change options
  // and create engines that are never run.
  Lib::ScopedLet<OrderingSP> proofOrdering(InferenceStore::instance()->ordering,
                                         ordering);
  Ordering::unsetGlobalOrdering();
  _alg = std::make_unique<Saturation::Discount>(*_problem, *env.options);
  // Replay uses the proof ordering explicitly and releases the global cache.
  Ordering::unsetGlobalOrdering();
}

template<typename Engine>
void InferenceReplayer::runGenerating(const ClauseStack& context)
{
  ASS(_alg);
  Engine rule(*_alg);
  runGenerating(rule, context);
}

template<typename Engine>
void InferenceReplayer::runForwardsSimp(const ClauseStack& context)
{
  ASS(_alg);
  Engine rule(*_alg);
  runForwardsSimp(rule, context);
}

void InferenceReplayer::replayInference(Unit* goal)
{
  if (!goal->isClause()) { return; }
  InferenceRecorder::instance()->setCurrentGoal(goal->asClause());
  ClauseStack context;
  auto parents = goal->getParents();
  while (parents.hasNext()) {
    Unit* parent = parents.next();
    if (!parent->isClause()) { return; }
    context.push(parent->asClause());
  }
  Lib::ScopedLet<bool> reconstruction(env.reconstruction, true);
  if (context.isEmpty()) { return; }

  switch (goal->inference().rule()) {
  case InferenceRule::RESOLUTION:
  case InferenceRule::CONSTRAINED_RESOLUTION:
    runGenerating<BinaryResolution>(context); break;
  case InferenceRule::SUPERPOSITION:
  case InferenceRule::CONSTRAINED_SUPERPOSITION:
    if (env.higherOrder()) { runGenerating<Superposition<true>>(context); }
    else { runGenerating<Superposition<false>>(context); }
    break;
  case InferenceRule::FACTORING:
    runGenerating<Factoring>(context); break;
  case InferenceRule::FORWARD_DEMODULATION:
    if (env.higherOrder()) { runForwardsSimp<ForwardDemodulation<true>>(context); }
    else { runForwardsSimp<ForwardDemodulation<false>>(context); }
    break;
  default:
    break;
  }
}

void InferenceReplayer::runGenerating(GeneratingInferenceEngine& rule,
                                     const ClauseStack& context)
{
  ReplayContext active(*_alg);
  for (Clause* parent : context) { active.activate(parent, /*resetAge=*/true); }
  auto result = rule.generateSimplify(context[0]);
  // Iterators perform inference work lazily. Drain them while the parents are
  // indexed; the recorder retains only candidates matching the proof goal.
  while (result.clauses.hasNext()) { result.clauses.next(); }
}

void InferenceReplayer::runForwardsSimp(ForwardSimplificationEngine& rule,
                                      const ClauseStack& context)
{
  ASS_EQ(context.size(), 2);
  ReplayContext active(*_alg);
  active.activate(context[1]);
  Clause* replacement = nullptr;
  ClauseIterator premises;
  rule.perform(context[0], replacement, premises);
}

} // namespace Shell
