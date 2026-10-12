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
#include "Inferences/FOOLParamodulation.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/HOL/CNFOnTheFly.hpp"
#include "Inferences/HOL/Cases.hpp"
#include "Inferences/HOL/CasesSimp.hpp"
#include "Inferences/HOL/Choice.hpp"
#include "Inferences/HOL/FlexFlexSimplify.hpp"
#include "Inferences/HOL/ImitateProject.hpp"
#include "Inferences/HOL/LeibnizEqualityElimination.hpp"
#include "Inferences/HOL/NegativeExtensionality.hpp"
#include "Inferences/HOL/PrimitiveInstantiation.hpp"
#include "Inferences/InnerRewriting.hpp"
#include "Inferences/SubsumptionEqualityResolution.hpp"
#include "Inferences/Superposition.hpp"
#include "Inferences/URResolution.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/TermIterators.hpp"
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
  Lib::ScopedLet<bool> reconstruction(env.reconstruction, true);
  if (context.isEmpty()) {
    replayParentlessAxiom(goal->asClause());
    return;
  }

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
    if (env.higherOrder()) { runGenerating<Superposition<true>>(context); }
    else { runGenerating<Superposition<false>>(context); }
    break;
  case InferenceRule::EQUALITY_RESOLUTION:
    runGenerating<EqualityResolution>(context); break;
  case InferenceRule::EQUALITY_FACTORING:
    runGenerating<EqualityFactoring>(context); break;
  case InferenceRule::FACTORING:
    runGenerating<Factoring>(context); break;
  case InferenceRule::FORWARD_DEMODULATION:
    if (env.higherOrder()) { runForwardsSimp<ForwardDemodulation<true>>(context); }
    else { runForwardsSimp<ForwardDemodulation<false>>(context); }
    break;
  case InferenceRule::FORWARD_SUBSUMPTION_DEMODULATION:
    runForwardsSimp<ForwardSubsumptionDemodulation<false>>(context); break;
  case InferenceRule::BACKWARD_DEMODULATION:
    if (env.higherOrder()) { runBackwardsSimp<BackwardDemodulation<true>>(context); }
    else { runBackwardsSimp<BackwardDemodulation<false>>(context); }
    break;
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
  case InferenceRule::PRIMITIVE_INSTANTIATION:
    runGenerating<PrimitiveInstantiation>(context); break;
  case InferenceRule::IMITATION:
  case InferenceRule::PROJECTION:
    runGenerating<ImitateProject>(context); break;
  case InferenceRule::LEIBNIZ_ELIMINATION:
    runGenerating<LeibnizEqualityElimination>(context); break;
  case InferenceRule::FLEX_FLEX_SIMPLIFICATION:
    ASS_EQ(context.size(), 1);
    FlexFlexSimplify().simplify(context[0]); break;
  case InferenceRule::FOOL_PARAMODULATION:
    if (env.higherOrder()) { runGenerating<Cases>(context); }
    else {
      FOOLParamodulation rule;
      runGenerating(rule, context);
    }
    break;
  case InferenceRule::CASES_SIMP: {
    ASS_EQ(context.size(), 1);
    auto result = CasesSimp().simplifyMany(context[0]);
    if (result.isSome()) {
      auto& clauses = result.unwrap();
      while (clauses.hasNext()) { clauses.next(); }
    }
    break;
  }
  case InferenceRule::HEURISTIC_INSTANTIATION: {
    LazyClausificationGIE rule;
    runGenerating(rule, context);
    break;
  }
  case InferenceRule::NEGATIVE_EXTENSIONALITY:
  case InferenceRule::SIGMA_PROXY_CLAUSIFICATION:
  case InferenceRule::SIGMA_PROXY_CLAUSIFICATION_SIMPLIFYING:
    replayWitnessInference(goal->asClause(), context); break;
  default:
    break; // not replayable yet
  }
}

void InferenceReplayer::replayWitnessInference(Clause* goal, const ClauseStack& context)
{
  ASS_EQ(context.size(), 1);
  // Include applications of each Skolem head, not just the symbol: a witness
  // reused by the formula index can have arbitrary instantiated dependencies.
  std::unordered_set<uint64_t> seen;
  for (Literal* literal : goal->iterLits()) {
    NonVariableNonTypeIterator terms(literal);
    while (terms.hasNext()) {
      TermList term(terms.next());
      if (term.isLambdaTerm()) { continue; }
      auto [head, args] = HOL::getHeadAndArgs(term);
      if (!head.isTerm() || head.isLambdaTerm() ||
          !env.signature->getFunction(head.term()->functor())->skolem() ||
          !seen.insert(term.content()).second) { continue; }
      InferenceRecorder::instance()->setReplayWitness(term);
      if (goal->inference().rule() == InferenceRule::NEGATIVE_EXTENSIONALITY) {
        runGenerating<NegativeExtensionality>(context);
      } else {
        LazyClausificationGIE rule;
        runGenerating(rule, context);
      }
      if (InferenceRecorder::instance()->getLastRecordedInferenceInformation()) { return; }
    }
  }
}

void InferenceReplayer::replayParentlessAxiom(Clause* goal)
{
  switch (goal->inference().rule()) {
  case InferenceRule::FUNCTIONAL_EXTENSIONALITY_AXIOM:
    HOL::create::functionalExtensionalityAxiom();
    break;
  case InferenceRule::HILBERTS_CHOICE_INSTANCE:
    for (Literal* literal : goal->iterLits()) {
      NonVariableNonTypeIterator terms(literal);
      while (terms.hasNext()) {
        TermList term(terms.next());
        if (!term.isApplication()) { continue; }
        TermList op = term.lhs();
        if (op.isTerm() && !op.isApplication() && !op.isLambdaTerm() &&
            (env.signature->isChoiceOperator(op.term()->functor()) ||
             env.signature->getFunction(op.term()->functor())->name() == "vEPSILON")) {
          Choice::createChoiceAxiom(op, term.rhs());
          if (InferenceRecorder::instance()->getLastRecordedInferenceInformation()) { return; }
        }
      }
    }
    break;
  default:
    break;
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
