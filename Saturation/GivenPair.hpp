/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file GivenPair.hpp
 * Defines class GivenPairAlgorithm
 *
 */

#ifndef __GivenPair__
#define __GivenPair__

#include "SaturationAlgorithm.hpp"

#include "Lib/BinaryHeap.hpp"

namespace Saturation {
class GivenPairAlgorithm: public SaturationAlgorithm {
public:
  GivenPairAlgorithm(Problem& prb, const Options& opt) : SaturationAlgorithm(prb, opt), _generating_container(opt) {}

  struct ByAge {
    static Comparison compare(std::pair<Clause *, Clause *> left, std::pair<Clause *, Clause *> right) {
      unsigned left_age = left.first->age() + left.second->age();
      unsigned right_age = right.first->age() + right.second->age();
      return Int::compare(left_age, right_age);
    }
  };

protected:
  MainLoopResult runImpl() override;
  void addNewClause(Clause* cl) override;
  void addInputClause(Clause* cl) override { addNewClause(cl); }
  void removeActiveOrPassiveClause(Clause* cl) override { NOT_IMPLEMENTED; }
  bool clausesFlushed() override { NOT_IMPLEMENTED; }
  ClauseContainer* getGeneratingClauseContainer() override { return &_generating_container; }
  ClauseContainer* getSimplifyingClauseContainer() override { return _active; }
  PassiveClauseContainer* getPassiveClauseContainer() override { return nullptr; }

  BinaryHeap<std::pair<Clause *, Clause *>, ByAge> by_age;

  ActiveClauseContainer _generating_container;
};
}
#endif
