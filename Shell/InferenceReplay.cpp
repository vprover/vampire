#include "Shell/InferenceReplay.hpp"
#include "Inferences/BackwardDemodulation.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/Superposition.hpp"
#include "Kernel/Inference.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include "Shell/InferenceRecorder.hpp"

namespace Shell {
void InferenceReplayer::replayInference(Kernel::Unit *u)
{
  auto it = u->getParents();
  ClauseStack stack;
  while (it.hasNext()) {
    auto parent = it.next();
    if (parent->isClause()) {
      stack.push((parent->asClause()));
    }
  }

  if (u->inference().rule() == InferenceRule::RESOLUTION) {
    BinaryResolution br;
    runGenerating(&br, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::FORWARD_DEMODULATION){
      ForwardDemodulation fd;
      runForwardsSimp(&fd,
      stack, u->asClause());
  }
  else if(u->inference().rule() == InferenceRule::BACKWARD_DEMODULATION){
      BackwardDemodulation bd;
      runBackwardsSimp(&bd,
      stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::SUPERPOSITION) {
    Inferences::Superposition sp;
    runGenerating(&sp,
                         stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::EQUALITY_RESOLUTION) {
    Inferences::EqualityResolution eq;
    runGenerating(&eq,
                         stack, u->asClause());
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
    Inferences::Factoring fact;
    runGenerating(&fact,
                         stack, u->asClause());
  }
  else {
    return; // not replayable yet
  }
  return;
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

  rule->attach(alg);

  auto activeContainer = alg->getActiveClauseContainer();
  for (auto c : context) {
    c->setStore(Clause::ACTIVE);
    c->setAge(0);
    activeContainer->add(c);
  }
  auto clauses = activeContainer->clauses();
  auto res = rule->generateSimplify(context[0]);

  while(res.clauses.hasNext()){
    //Iterate through genereation of all clauses
    res.clauses.next();
  }
  removeAllActiveClauses();
  // // tear down saturation algorithm
  rule->detach();
  // alg->~SaturationAlgorithm();
  Ordering::unsetGlobalOrdering();

  return nullptr;
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
  rule->perform(clause, replacement, clauses);
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

void InferenceReplayer::runBackwardsSimp(Inferences::BackwardSimplificationEngine *rule,
                                         ClauseStack context, Clause *goal)
{
  Problem p;
  ASS(alg != nullptr);

  rule->attach(alg);
  ClauseContainer *simplClauseContainer = alg->getSimplifyingClauseContainer();

  // Backward simplification, so we add the clause to be simplified to the simplifying container
  context[0]->setStore(Clause::ACTIVE);
  simplClauseContainer->add(context[0]);

  Clause *clause = Clause::fromClause(context[1]);

  Inferences::BwSimplificationRecordIterator simpls;
  rule->perform(clause, simpls);

  while(simpls.hasNext()){
    simpls.next();
  }

  rule->detach();
  Ordering::unsetGlobalOrdering();
}

} // namespace Shell
