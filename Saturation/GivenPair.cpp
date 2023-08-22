/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "GivenPair.hpp"

#include "Kernel/LiteralSelector.hpp"

namespace Saturation {
MainLoopResult GivenPairAlgorithm::runImpl() {
  while(!by_age.isEmpty()) {
    auto given = by_age.pop();
    Clause *left = given.first;
    Clause *right = given.second;

    _generating_container.add(left);
    // TODO check whether clause is indicated redundant
    auto left_children = _generator->generateSimplify(right).clauses;
    while(left_children.hasNext())
      addNewClause(left_children.next());
    _generating_container.remove(left);

    _generating_container.add(right);
    // TODO check whether clause is indicated redundant
    auto right_children = _generator->generateSimplify(left).clauses;
    while(right_children.hasNext())
      addNewClause(right_children.next());
    _generating_container.remove(right);
  }
  return Statistics::TerminationReason::SATISFIABLE;
}

void GivenPairAlgorithm::addNewClause(Clause *cl) {
start:
  if(isRefutation(cl))
    throw RefutationFoundException(cl);

  // immediate simplification
  while(true) {
    Clause *simplified = _immediateSimplifier->simplify(cl);
    if(!simplified)
      // TODO ref counts
      return;
    if(simplified == cl)
      break;
    cl = simplified;
  }

  // "forward" simplification from active set
  FwSimplList::Iterator fsit(_fwSimplifiers);
  while(fsit.hasNext()) {
    ForwardSimplificationEngine* fse=fsit.next();
    Clause *simplified = nullptr;
    ClauseIterator premises;
    if(fse->perform(cl, simplified, premises)) {
      if(!simplified)
        return;
      cl = simplified;
      goto start;
    }
  }

  //TODO "backward" simplification

  if(env.options->showActive())
    std::cout << "[SA] active: " << cl->toString() << std::endl;

  _selector->select(cl);
  cl->setStore(Clause::ACTIVE);
  env.statistics->activeClauses++;
  _active->add(cl);

  ClauseIterator it = _active->clauses();
  while(it.hasNext())
    // TODO ref counts
    by_age.insert({cl, it.next()});
}
}
