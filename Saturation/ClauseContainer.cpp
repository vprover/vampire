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
 * @file ClauseContainer.cpp
 * Implementing ClauseContainer and its descendants.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"
#include "Shell/Statistics.hpp"

#include "Indexing/LiteralIndexingStructure.hpp"

#include "SaturationAlgorithm.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

#include "ClauseContainer.hpp"

namespace Saturation
{

using namespace Kernel;
using namespace Indexing;

/////////////////   UnprocessedClauseContainer   //////////////////////

UnprocessedClauseContainer::~UnprocessedClauseContainer()
{
  while (!_data.isEmpty()) {
    Clause* cl=_data.pop_back();
    ASS_EQ(cl->store(), Clause::UNPROCESSED);
    cl->setStore(Clause::NONE);
  }
}

void UnprocessedClauseContainer::add(Clause* c)
{
  _data.push_back(c);
  addedEvent.fire(c);
}

Clause* UnprocessedClauseContainer::pop()
{
  Clause* res=_data.pop_front();
  selectedEvent.fire(res);
  return res;
}

void PassiveClauseContainer::updateLimits(long long estReachableCnt)
{
  ASS_GE(estReachableCnt,0);

  // optimization: if the estimated number of clause-selections is higher than the number of clauses in passive,
  // we already conclude that we will select all clauses, so we set the limits accordingly.
  if (estReachableCnt > static_cast<long long>(sizeEstimate())) {
    setLimitsToMax();
    return;
  }
  // otherwise we run the simulation and set the limits accordingly
  Clause::requestAux();
  simulationInit();

  long long remains=estReachableCnt;
  while (simulationHasNext() && remains > 0)
  {
    simulationPopSelected();
    remains--;
  }
  bool atLeastOneLimitTightened = setLimitsFromSimulation();
  Clause::releaseAux();

  if (atLeastOneLimitTightened && env.options->lrsRetroactiveDeletes()) {
    // let's notify ourselves (the PassiveClauseContainer) ...
    onLimitsUpdated();
    // ... and also the getActiveClauseContainer, about the tightening limits
    getSaturationAlgorithm()->getActiveClauseContainer()->onLimitsUpdated(this);
  }
}

/////////////////   ActiveClauseContainer   //////////////////////

void ActiveClauseContainer::add(Clause* c)
{
  TIME_TRACE("add clause")

  ASS(c->store()==Clause::ACTIVE);
  ALWAYS(_clauses.insert(c));
  addedEvent.fire(c);
}

/**
 * Remove Clause from the Active store. Should be called only
 * when the Clause is no longer needed by the inference process
 * (i.e. was backward subsumed/simplified), as it can result in
 * deletion of the clause.
 */
void ActiveClauseContainer::remove(Clause* c)
{
  ASS(c->store()==Clause::ACTIVE);
  ALWAYS(_clauses.remove(c));
  removedEvent.fire(c);
} // Active::ClauseContainer::remove

void ActiveClauseContainer::onLimitsUpdated(PassiveClauseContainer* limits)
{
  ASS(limits);
  if (!limits->mayBeAbleToDiscriminateChildrenOnLimits()) {
    return;
  }

  static Stack<Clause*> toRemove(64);
  toRemove.reset();

  auto rit = _clauses.iter();
  while (rit.hasNext()) {
    Clause* cl=rit.next();
    ASS(cl);

    if (limits->allChildrenNecessarilyExceedLimits(cl, cl->numSelected()))
    {
      ASS(cl->store()==Clause::ACTIVE);
      toRemove.push(cl);
    }
  }

#if OUTPUT_LRS_DETAILS
  if (toRemove.isNonEmpty()) {
    cout<<toRemove.size()<<" active deleted\n";
  }
#endif

  while (toRemove.isNonEmpty()) {
    Clause* removed=toRemove.pop();
    ASS(removed->store()==Clause::ACTIVE);

    RSTAT_CTR_INC("clauses discarded from active on limit update");
    env.statistics->discardedNonRedundantClauses++;

    remove(removed);
    // ASS_NEQ(removed->store(), Clause::ACTIVE); -- the remove could have deleted the clause - do not touch!
  }
}

}

