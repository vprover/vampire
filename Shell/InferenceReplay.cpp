#include "Shell/InferenceReplay.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/Superposition.hpp"
#include "Inferences/ForwardSubsumptionAndResolution.hpp"
#include "Kernel/Inference.hpp"
#include "Test/TestUtils.hpp"
namespace Shell {
Clause *InferenceReplayer::replayInference(Kernel::Unit *u)
{
  auto it = u->getParents();
  ClauseStack stack;
  while (it.hasNext()) {
    auto parent = it.next();
    if (parent->isClause()) {
      stack.push((parent->asClause()));
    }
    else {
      return nullptr; // not replayable yet
    }
  }

  if (u->inference().rule() == InferenceRule::RESOLUTION) {
    BinaryResolution br;
    return runGenerating(&br, stack, u->asClause());
  }
  //else if (u->inference().rule() == InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION) {
  //  ForwardSubsumptionAndResolution fsr(true);
  //  runForwardsSimp(&fsr,
  //                  stack, u->asClause());
  //}
  // else if (u->inference().rule() == InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION){
  //     BackwardSubsumptionAndResolution bsr(false, false, true, false);
  //     runBackwardsSimp(&bsr,
  //     stack, u->asClause());
  // }
  // else if (u->inference().rule() == InferenceRule::FORWARD_DEMODULATION){
  //     ForwardDemodulation fd;
  //     runForwardsSimp(&fd,
  //     stack, u->asClause());
  // }
  else if (u->inference().rule() == InferenceRule::SUPERPOSITION) {
    Inferences::Superposition sp;
    return runGenerating(&sp,
                         stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::EQUALITY_RESOLUTION) {
    Inferences::EqualityResolution eq;
    return runGenerating(&eq,
                         stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::FACTORING) {
    Inferences::Factoring fact;
    return runGenerating(&fact,
                         stack, u->asClause());
  }
  else {
    return nullptr; // not replayable yet
  }
  return nullptr;
}

template <typename Iterator>
Clause *getMatchingClauseIter(Clause *goal, Iterator *clauses)
{
  Clause *foundClause = nullptr;
  // It seems like one needs to iterate through all clauses to
  // preserve some internal state? Not sure why though.
  while (clauses->hasNext()) {
    Clause *c = clauses->next();
    if (foundClause == nullptr) {
      if (Test::TestUtils::eqModACRect(c, goal)) {
        foundClause = c;
      }
    }
  }
  return foundClause;
}

Clause *getMatchingClause(Clause *goal, std::initializer_list<Clause *> clauses)
{
  Clause *foundClause = nullptr;
  // It seems like one needs to iterate through all clauses to
  // preserve some internal state? Not sure why though.
  for (auto c : clauses) {
    if (foundClause == nullptr) {
      if (Test::TestUtils::eqModACRect(c, goal)) {
        foundClause = c;
      }
    }
  }
  return foundClause;
}

/*void InferenceReplayer::runBackwardsSimp(Inferences::BackwardSimplificationEngine *rule,
                                         ClauseStack context, Clause *goal)
{
  Problem p;
  ASS(alg != nullptr);

  rule->attach(alg);
  ClauseContainer *simplClauseContainer = alg->getSimplifyingClauseContainer();

  // Backward simplification, so we add the clause to be simplified to the simplifying container
  context[1]->setStore(Clause::ACTIVE);
  simplClauseContainer->add(context[0]);

  Clause *clause = Clause::fromClause(context[1]);
  Clause *replacement = nullptr;
  Kernel::ClauseIterator clauses;
  Inferences::BwSimplificationRecordIterator simpls;
  rule->perform(clause, simpls);
  while (simpls.hasNext()) {
    auto rec = simpls.next();
    if (Test::TestUtils::eqModACRect(rec.replacement, goal)) {
      *out << "MATCHES GOAL!";
    }
    else {
      ASSERTION_VIOLATION
    }
    *out << "Replacement clause: " << replacement->toString() << "\n";
  }
  auto iter = alg->getActiveClauseContainer()->clauses();
  while (iter.hasNext()) {
    Clause *c = iter.next();
    *out << "Active clause: " << c->toString() << "\n";
    alg->getActiveClauseContainer()->remove(c);
  }
  rule->detach();
  Ordering::unsetGlobalOrdering();
}*/

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

  rule->attach(alg);

  auto activeContainer = alg->getActiveClauseContainer();
  for (auto c : context) {
    c->setStore(Clause::ACTIVE);
    c->setAge(0);
    activeContainer->add(c);
  }
  auto clauses = activeContainer->clauses();
  auto res = rule->generateSimplify(context[0]);
  // run checks
  Clause *c = getMatchingClauseIter(goal, &res.clauses);

  if (c == nullptr) {
    ASSERTION_VIOLATION_REP("Houston, we have a problem!");
  }
  removeAllActiveClauses();
  // // tear down saturation algorithm
  rule->detach();
  // alg->~SaturationAlgorithm();
  Ordering::unsetGlobalOrdering();

  return c;
}

void InferenceReplayer::runForwardsSimp(ForwardSimplificationEngine *rule,
                                        ClauseStack context, Clause *goal)
{
  Problem p;
  ASS(alg);
  rule->attach(alg);

  ClauseContainer *simplClauseContainer = alg->getSimplifyingClauseContainer();

  context[1]->setStore(Clause::ACTIVE);
  simplClauseContainer->add(context[1]);

  Clause *clause = context[0];
  Clause *replacement = nullptr;
  Kernel::ClauseIterator clauses;
  auto res = rule->perform(clause, replacement, clauses);
  if (res) {
    if (replacement != nullptr) {
      Clause *c = getMatchingClause(goal, {replacement});
      if (c == nullptr) {
        ASSERTION_VIOLATION_REP("Houston, we have a problem!");
      }
    }
  }
  else {
    ASSERTION_VIOLATION
  }

  removeAllActiveClauses();
  rule->detach();
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
}
