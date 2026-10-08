#include "Shell/InferenceReplay.hpp"
#include "Inferences/BackwardDemodulation.hpp"
#include "Inferences/BackwardSubsumptionDemodulation.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/Condensation.hpp"
#include "Inferences/EqualityFactoring.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/ExtensionalityResolution.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/FastCondensation.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/ForwardSubsumptionDemodulation.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/InnerRewriting.hpp"
#include "Inferences/SubsumptionEqualityResolution.hpp"
#include "Inferences/Superposition.hpp"
#include "Inferences/URResolution.hpp"
#include "Kernel/Inference.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include "Shell/InferenceRecorder.hpp"

#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Lib/Environment.hpp"
#include "Lib/ScopedLet.hpp"
#include "Shell/SimplificationReplay.hpp"
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

template<typename Engine>
void InferenceReplayer::runBackwardsSimp(const ClauseStack& context)
{
  ASS(_alg);
  Engine rule(*_alg);
  runBackwardsSimp(rule, context);
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
  if (context.isEmpty()) { return; }
  Lib::ScopedLet<bool> reconstruction(env.reconstruction, true);

  switch (goal->inference().rule()) {
  case InferenceRule::RESOLUTION:
  case InferenceRule::CONSTRAINED_RESOLUTION:
    runGenerating<BinaryResolution>(context); break;
  case InferenceRule::EXTENSIONALITY_RESOLUTION:
    runGenerating<ExtensionalityResolution>(context); break;
  case InferenceRule::UNIT_RESULTING_RESOLUTION:
    runGenerating<URResolution<false>>(context); break;
  case InferenceRule::SUPERPOSITION:
  case InferenceRule::CONSTRAINED_SUPERPOSITION:
    runGenerating<Superposition<false>>(context); break;
  case InferenceRule::EQUALITY_RESOLUTION:
    runGenerating<EqualityResolution>(context); break;
  case InferenceRule::EQUALITY_FACTORING:
    runGenerating<EqualityFactoring>(context); break;
  case InferenceRule::FACTORING:
    runGenerating<Factoring>(context); break;
  case InferenceRule::FORWARD_DEMODULATION:
    runForwardsSimp<ForwardDemodulation<false>>(context); break;
  case InferenceRule::FORWARD_SUBSUMPTION_DEMODULATION:
    runForwardsSimp<ForwardSubsumptionDemodulation<false>>(context); break;
  case InferenceRule::BACKWARD_DEMODULATION:
    runBackwardsSimp<BackwardDemodulation<false>>(context); break;
  case InferenceRule::BACKWARD_SUBSUMPTION_DEMODULATION:
    runBackwardsSimp<BackwardSubsumptionDemodulation<false>>(context); break;
  case InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION:
    ASS_EQ(context.size(), 2);
    SimplificationReplay::subsumptionResolution(context[0], context[1]); break;
  case InferenceRule::FORWARD_LITERAL_REWRITING: {
    ASS_EQ(context.size(), 2);
    SimplificationReplay::literalRewriting(context[0], context[1]);
    break;
  }
  case InferenceRule::CONDENSATION:
    ASS_EQ(context.size(), 1);
    replayCondensation(context[0]); break;
  case InferenceRule::SUBSUMPTION_EQUALITY_RESOLUTION:
    ASS_EQ(context.size(), 1);
    SubsumptionEqualityResolution().simplify(context[0]); break;
  case InferenceRule::INNER_REWRITING:
    ASS(_alg);
    ASS_EQ(context.size(), 1);
    InnerRewriting(*_alg).simplify(context[0]); break;
  case InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION:
    ASS_EQ(context.size(), 1);
    EqResWithDeletion().apply(context[0]); break;
  default:
    break; // not replayable yet
  }
}

void InferenceReplayer::replayCondensation(Clause* premise)
{
  // Both engines use the same inference name. Fast condensation keeps the
  // remaining literals unchanged; general condensation can instantiate them.
  // Try both independently of the original search options.
  if (env.higherOrder()) {
    FastCondensation<true>().simplify(premise);
  } else {
    FastCondensation<false>().simplify(premise);
  }
  if (!InferenceRecorder::instance()->getLastRecordedInferenceInformation()) {
    Condensation().simplify(premise);
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

void InferenceReplayer::runBackwardsSimp(BackwardSimplificationEngine& rule,
                                       const ClauseStack& context)
{
  ASS_EQ(context.size(), 2);
  ReplayContext active(*_alg);
  active.activate(context[0]);
  BwSimplificationRecordIterator simplifications;
  // Keep the original side parent: a copy would change its proof ID.
  rule.perform(context[1], simplifications);
  while (simplifications.hasNext()) { simplifications.next(); }
}

} // namespace Shell
