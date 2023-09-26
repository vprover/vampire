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
  while(true) {
    unsigned left_index, right_index;
    std::cin >> left_index >> right_index;

    Clause *left = by_number.get(left_index);
    Clause *right = by_number.get(right_index);

    _generating_container.add(left);
    // TODO check whether clause is indicated redundant
    auto left_children = _generator->generateSimplify(right).clauses;
    while(left_children.hasNext())
      addNewClause(left_children.next());
    _generating_container.remove(left);
  }
}

void GivenPairAlgorithm::addNewClause(Clause *cl) {
start:
  if(env.options->showNew())
    std::cout << "[SA] new: " << cl->toString() << std::endl;

  if(isRefutation(cl))
    throw RefutationFoundException(cl);

  // immediate simplification
  while(true) {
    Clause *simplified = _immediateSimplifier->simplify(cl);
    if(!simplified) {
      // TODO ref counts
      if(env.options->showReductions())
        std::cout << "[SA] deleted: " << cl->toString() << std::endl;
      return;
    }

    if(simplified == cl)
      break;

    if(env.options->showReductions())
      std::cout << "[SA] replaced: " << cl->toString() << " with " << simplified->toString() << std::endl;
    cl = simplified;
  }

  // "forward" simplification from active set
  FwSimplList::Iterator fsit(_fwSimplifiers);
  while(fsit.hasNext()) {
    ForwardSimplificationEngine *fse=fsit.next();
    Clause *simplified = nullptr;
    ClauseIterator premises;
    if(fse->perform(cl, simplified, premises)) {
      if(!simplified) {
        if(env.options->showReductions())
          std::cout << "[SA] deleted: " << cl->toString() << std::endl;
        return;
      }

      if(env.options->showReductions())
        std::cout << "[SA] replaced: " << cl->toString() << " with " << simplified->toString() << std::endl;
      cl = simplified;
      goto start;
    }
  }

  // "backward" simplification into the active set
  BwSimplList::Iterator bsit(_bwSimplifiers);
  while (bsit.hasNext()) {
    BackwardSimplificationEngine *bse=bsit.next();
    BwSimplificationRecordIterator simplifications;
    bse->perform(cl, simplifications);
    while(simplifications.hasNext()) {
      BwSimplificationRecord record = simplifications.next();
      Clause *redundant = record.toRemove;
      Clause *replacement = record.replacement;

      _active->remove(redundant);
      if(!replacement) {
        if(env.options->showReductions())
          std::cout << "[SA] deleted: " << redundant->toString() << std::endl;
        continue;
      }

      if(env.options->showReductions())
        std::cout << "[SA] replaced: " << redundant->toString() << " with " << replacement->toString() << std::endl;
      addNewClause(replacement);
    }
  }

  if(env.options->showActive())
    std::cout << "[SA] active: " << cl->toString() << std::endl;
  _selector->select(cl);
  cl->setStore(Clause::ACTIVE);
  env.statistics->activeClauses++;
  _active->add(cl);
  by_number.insert(cl->number(), cl);
}
}
