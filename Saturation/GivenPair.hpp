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

protected:
  MainLoopResult runImpl() override;
  void addNewClause(Clause* cl) override;
  void addInputClause(Clause* cl) override { addNewClause(cl); }
  void removeActiveOrPassiveClause(Clause* cl) override { NOT_IMPLEMENTED; }
  bool clausesFlushed() override { NOT_IMPLEMENTED; }
  ClauseContainer* getGeneratingClauseContainer() override { return &_generating_container; }
  ClauseContainer* getSimplifyingClauseContainer() override { return _active; }
  PassiveClauseContainer* getPassiveClauseContainer() override { return nullptr; }

  ActiveClauseContainer _generating_container;

  DHMap<unsigned, Clause *> by_number;
};
}
#endif
