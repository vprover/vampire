#include "Shell/InferenceReplay.hpp"
#include "Inferences/BackwardDemodulation.hpp"
#include "Inferences/BackwardSubsumptionAndResolution.hpp"
#include "Inferences/BackwardSubsumptionDemodulation.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/Condensation.hpp"
#include "Inferences/EqualityFactoring.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/ExtensionalityResolution.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/FastCondensation.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/ForwardLiteralRewriting.hpp"
#include "Inferences/ForwardSubsumptionDemodulation.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/InnerRewriting.hpp"
#include "Inferences/SubsumptionEqualityResolution.hpp"
#include "Inferences/Superposition.hpp"
#include "Inferences/URResolution.hpp"
#include "Kernel/Inference.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include "Shell/InferenceRecorder.hpp"

#include <unordered_set>

namespace Shell {
using namespace Kernel;

void InferenceReplayer::replayInference(Kernel::Unit *u)
{
  auto it = u->getParents();
  ClauseStack stack;
  while (it.hasNext()) {
    Unit* parent = it.next();
    if (!parent->isClause()) { return; }
    stack.push(parent->asClause());
  }
  if (u->inference().rule() == InferenceRule::CONDENSATION) {
    ASS_EQ(stack.size(), 1);
    // Both engines use the same inference name. Fast condensation keeps the
    // remaining literals unchanged; general condensation can instantiate them.
    // Try both, independently of the options used during the original search.
    if (env.higherOrder()) {
      Inferences::FastCondensation<true> fast;
      fast.simplify(stack[0]);
    } else {
      Inferences::FastCondensation<false> fast;
      fast.simplify(stack[0]);
    }
    if (!InferenceRecorder::instance()->getLastRecordedInferenceInformation()) {
      Inferences::Condensation general;
      general.simplify(stack[0]);
    }
  }
  else if (u->inference().rule() == InferenceRule::RESOLUTION ||
           u->inference().rule() == InferenceRule::CONSTRAINED_RESOLUTION) {
    BinaryResolution br(*alg);
    runGenerating(&br, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::EXTENSIONALITY_RESOLUTION) {
    ExtensionalityResolution er(*alg);
    runGenerating(&er, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::UNIT_RESULTING_RESOLUTION) {
    URResolution<false> urr(*alg);
    runGenerating(&urr, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::FORWARD_LITERAL_REWRITING) {
    ForwardLiteralRewriting flr(*alg, stack[1]);
    runForwardsSimp(&flr, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::SUBSUMPTION_EQUALITY_RESOLUTION) {
    SubsumptionEqualityResolution ser;
    ser.simplify(stack[0]);
  }
  else if (u->inference().rule() == InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION) {
    BackwardSubsumptionAndResolution<false> bsr(*alg);
    runBackwardsSimp(&bsr, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::FORWARD_DEMODULATION) {
    ForwardDemodulation<false> fd(*alg);
    runForwardsSimp(&fd, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::BACKWARD_DEMODULATION) {
    BackwardDemodulation<false> bd(*alg);
    runBackwardsSimp(&bd, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::FORWARD_SUBSUMPTION_DEMODULATION) {
    ForwardSubsumptionDemodulation<false> fsd(*alg);
    runForwardsSimp(&fsd, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::BACKWARD_SUBSUMPTION_DEMODULATION) {
    BackwardSubsumptionDemodulation<false> bsd(*alg);
    runBackwardsSimp(&bsd, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::INNER_REWRITING) {
    InnerRewriting ir(*alg);
    ir.simplify(stack[0]);
  }
  else if (u->inference().rule() == InferenceRule::SUPERPOSITION ||
           u->inference().rule() == InferenceRule::CONSTRAINED_SUPERPOSITION) {
    Inferences::Superposition<false> sp(*alg);
    runGenerating(&sp, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::EQUALITY_RESOLUTION) {
    Inferences::EqualityResolution eq(*alg);
    runGenerating(&eq, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::EQUALITY_FACTORING) {
    Inferences::EqualityFactoring eq(*alg);
    runGenerating(&eq, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION) {
    Inferences::EqResWithDeletion eq;
    Problem p;
    auto ul = UnitList::empty();
    UnitList::pushFromIterator(ClauseStack::Iterator(stack), ul);
    p.addUnits(ul);
    env.setMainProblem(&p);
    eq.apply(p);
  }
  else if (u->inference().rule() == InferenceRule::FACTORING) {
    Inferences::Factoring fact(*alg);
    runGenerating(&fact, stack, u->asClause());
  }
  else {
    return; // not replayable yet
  }
}

Clause *InferenceReplayer::runGenerating(GeneratingInferenceEngine *rule,
                                         ClauseStack context, Clause *goal)
{
  // init problem
  ASS(alg != nullptr);
  Problem p;
  auto ul = UnitList::empty();
  UnitList::pushFromIterator(ClauseStack::Iterator(context), ul);
  p.addUnits(ul);

  env.setMainProblem(&p);

  auto activeContainer = alg->getActiveClauseContainer();
  std::unordered_set<unsigned> activated;
  for (auto c : context) {
    // A self-inference lists one clause in more than one parent position.
    // Keep those positions in `context`, but an active container owns each
    // clause number only once.
    if (!activated.insert(c->number()).second) {
      continue;
    }
    c->setStore(Clause::ACTIVE);
    c->setAge(0);
    activeContainer->add(c);
  }
  auto res = rule->generateSimplify(context[0]);

  while(res.clauses.hasNext()){
    res.clauses.next();
  }
  removeAllActiveClauses();
  Ordering::unsetGlobalOrdering();

  return nullptr;
}

void InferenceReplayer::runForwardsSimp(ForwardSimplificationEngine *rule,
                                        ClauseStack context, Clause *goal)
{
  Problem p;
  ASS(alg);
  removeAllActiveClauses();
  ClauseContainer *simplClauseContainer = alg->getSimplifyingClauseContainer();
  context[1]->setStore(Clause::ACTIVE);
  simplClauseContainer->add(context[1]);
  Clause *clause = context[0];
  Clause *replacement = nullptr;
  Kernel::ClauseIterator clauses;
  rule->perform(clause, replacement, clauses);
  alg->getActiveClauseContainer()->remove(context[1]);
  removeAllActiveClauses();
  Ordering::unsetGlobalOrdering();
}

void InferenceReplayer::removeAllActiveClauses()
{
  auto iter = alg->getActiveClauseContainer()->clauses();
  while (iter.hasNext()) {
    Clause *c = iter.next();
    alg->getActiveClauseContainer()->remove(c);
  }
}

void InferenceReplayer::runBackwardsSimp(Inferences::BackwardSimplificationEngine *rule,
                                         ClauseStack context, Clause *goal)
{
  Problem p;
  ASS(alg != nullptr);
  removeAllActiveClauses();
  ClauseContainer *simplClauseContainer = alg->getSimplifyingClauseContainer();

  // Backward simplification, so we add the clause to be simplified to the simplifying container
  context[0]->setStore(Clause::ACTIVE);
  simplClauseContainer->add(context[0]);

  Inferences::BwSimplificationRecordIterator simpls;
  // Keep the original side parent: copying it changes its proof ID and makes
  // the recorded substitution refer to a parent that is not in the proof.
  rule->perform(context[1], simpls);

  while(simpls.hasNext()){
    simpls.next();
  }
  removeAllActiveClauses();
  Ordering::unsetGlobalOrdering();
}

} // namespace Shell
