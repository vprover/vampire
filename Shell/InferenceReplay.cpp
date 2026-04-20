#include "Shell/InferenceReplay.hpp"
#include "Inferences/BackwardDemodulation.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/EqualityFactoring.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/Superposition.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/Rectify.hpp"

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
    BinaryResolution br(*alg);
    runGenerating(&br, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::FORWARD_DEMODULATION){
      ForwardDemodulationReplay fd(*alg);
      runGenerating(&fd,
      stack, u->asClause());
  }
  else if(u->inference().rule() == InferenceRule::BACKWARD_DEMODULATION){
      BackwardDemodulation<false> bd(*alg);
      runBackwardsSimp(&bd,
      stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::SUPERPOSITION) {
    Inferences::Superposition sp(*alg);
    runGenerating(&sp,
                         stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::EQUALITY_RESOLUTION) {
    Inferences::EqualityResolution eq(*alg);
    runGenerating(&eq,
                         stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION) {

    auto ul = UnitList::empty();
    UnitList::pushFromIterator(ClauseStack::Iterator(stack), ul);
    Problem p(ul);
    env.setMainProblem(&p);
    Inferences::EqResWithDeletion eq;
    eq.apply(p);
  }
  else if(u->inference().rule() == InferenceRule::EQUALITY_FACTORING){
      auto ul = UnitList::empty();
      UnitList::pushFromIterator(ClauseStack::Iterator(stack), ul);
      Problem p(ul);      
      env.setMainProblem(&p);
      Inferences::EqualityFactoring eqf(*alg);
      runGenerating(&eqf, stack, u->asClause());
  }
  else if (u->inference().rule() == InferenceRule::FACTORING) {
    Inferences::Factoring fact(*alg);
    runGenerating(&fact,
                         stack, u->asClause());
  } else if (u->inference().rule() == InferenceRule::RECTIFY) {
    FormulaUnit *fu = static_cast<FormulaUnit *>(u->getParents().next());
    Rectify::rectify(fu);
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

  auto activeContainer = alg->getActiveClauseContainer();
  for (auto c : context) {
    c->setStore(Clause::ACTIVE);
    c->setAge(0);
    activeContainer->add(c);
  }
  auto clauses = activeContainer->clauses();
  auto res = rule->generateSimplify(context[0]);

  while(res.clauses.hasNext()){
    //Iterate through generation of all clauses
    res.clauses.next();
    if(InferenceRecorder::instance()->hasRecordedInference()){
      break;
    }
  }
  removeAllActiveClauses();

  // alg->~SaturationAlgorithm();
  Ordering::unsetGlobalOrdering();

  return nullptr;
}

void InferenceReplayer::runForwardsSimp(ForwardSimplificationEngine *rule,
                                        ClauseStack context, Clause *goal)
{
  Problem p;
  ASS(alg);
  ClauseContainer *simplClauseContainer = alg->getSimplifyingClauseContainer();
  context[1]->setStore(Clause::ACTIVE);
  simplClauseContainer->add(context[1]);
  Clause *clause = context[0];
  Clause *replacement = nullptr;
  Kernel::ClauseIterator clauses;
  rule->perform(clause, replacement, clauses);
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

  Ordering::unsetGlobalOrdering();
}

} // namespace Shell
