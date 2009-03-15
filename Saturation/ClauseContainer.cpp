/**
 * @file ClauseContainer.cpp
 * Implementing ClauseContainer and its descendants.
 */

#include "../Lib/Environment.hpp"

#include "../Kernel/Clause.hpp"

#include "../Shell/Statistics.hpp"

#include "SaturationAlgorithm.hpp"

#include "ClauseContainer.hpp"

using namespace Kernel;
using namespace Saturation;

void ClauseContainer::addClauses(ClauseIterator cit)
{
  while(cit.hasNext()) {
    add(cit.next());
  }
}

void RandomAccessClauseContainer::removeClauses(ClauseIterator cit)
{
  while(cit.hasNext()) {
    remove(cit.next());
  }
}

UnprocessedClauseContainer::~UnprocessedClauseContainer()
{
  while(!_data.isEmpty()) {
    Clause* cl=_data.pop();
    cl->setStore(Clause::NONE);
  }
}

void UnprocessedClauseContainer::add(Clause* c)
{
  _data.push(c);
  c->setStore(Clause::UNPROCESSED);
  env.statistics->generatedClauses++;
  addedEvent.fire(c);
}

Clause* UnprocessedClauseContainer::pop()
{
  Clause* res=_data.pop();
  selectedEvent.fire(res);
  return res;
}

/**
 * Attach to the SaturationAlgorithm object.
 *
 * This method is being called in the SaturationAlgorithm constructor,
 * so no virtual methods of SaturationAlgorithm should be called.
 */
void PassiveClauseContainer::attach(SaturationAlgorithm* salg)
{
  CALL("PassiveClauseContainer::attach");
  ASS(!_salg);

  _salg=salg;
  _limitChangeSData=_salg->getLimits()->changedEvent.subscribe(
      this, &PassiveClauseContainer::onLimitsUpdated);
}
/**
 * Detach from the SaturationAlgorithm object.
 *
 * This method is being called in the SaturationAlgorithm destructor,
 * so no virtual methods of SaturationAlgorithm should be called.
 */
void PassiveClauseContainer::detach()
{
  CALL("PassiveClauseContainer::detach");
  ASS(_salg);

  _limitChangeSData->unsubscribe();
  _salg=0;
}


void ActiveClauseContainer::add(Clause* c)
{
  c->setStore(Clause::ACTIVE);
  env.statistics->activeClauses++;
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
  ASS_EQ(c->store(), Clause::ACTIVE);

  removedEvent.fire(c);
  c->setStore(Clause::NONE);
}
