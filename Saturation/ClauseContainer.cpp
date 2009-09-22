/**
 * @file ClauseContainer.cpp
 * Implementing ClauseContainer and its descendants.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Set.hpp"
#include "../Lib/Stack.hpp"
#include "../Kernel/Clause.hpp"
#include "../Shell/Statistics.hpp"

#include "../Indexing/LiteralIndexingStructure.hpp"

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

/**
 * Attach to the SaturationAlgorithm object.
 *
 * This method is being called in the SaturationAlgorithm constructor,
 * so no virtual methods of SaturationAlgorithm should be called.
 */
void RandomAccessClauseContainer::attach(SaturationAlgorithm* salg)
{
  CALL("RandomAccessClauseContainer::attach");
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
void RandomAccessClauseContainer::detach()
{
  CALL("RandomAccessClauseContainer::detach");
  ASS(_salg);

  _limitChangeSData->unsubscribe();
  _salg=0;
}

UnprocessedClauseContainer::~UnprocessedClauseContainer()
{
  while(!_data.isEmpty()) {
    Clause* cl=_data.pop();
    ASS_EQ(cl->store(), Clause::UNPROCESSED);
    cl->setStore(Clause::NONE);
  }
}

void UnprocessedClauseContainer::add(Clause* c)
{
  _data.push(c);
  addedEvent.fire(c);
}

Clause* UnprocessedClauseContainer::pop()
{
  Clause* res=_data.pop();
  selectedEvent.fire(res);
  return res;
}


void ActiveClauseContainer::add(Clause* c)
{
  _size++;

  ASS(c->store()==Clause::ACTIVE);
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
  ASS(c->store()==Clause::ACTIVE || c->store()==Clause::REACTIVATED);

  _size--;

  removedEvent.fire(c);
}

void ActiveClauseContainer::onLimitsUpdated(LimitsChangeType change)
{
  if(change==LIMITS_LOOSENED) {
    return;
  }
  LiteralIndexingStructure* gis=getSaturationAlgorithm()->getIndexManager()
      ->getGeneratingLiteralIndexingStructure();
  if(!gis) {
    return;
  }
  Limits* limits=getSaturationAlgorithm()->getLimits();

  if(!limits->ageLimited() || !limits->weightLimited()) {
    return;
  }
  int ageLimit=limits->ageLimit();
  int weightLimit=limits->weightLimit();

  Set<Clause*> checked;
  static Stack<Clause*> toRemove(64);
  SLQueryResultIterator rit=gis->getAll();
  while(rit.hasNext()) {
    Clause* cl=rit.next().clause;
    if(cl->age()<ageLimit || checked.contains(cl)) {
      continue;
    }
    checked.insert(cl);

    bool shouldRemove;
    if(cl->age()>ageLimit) {
      shouldRemove=cl->getEffectiveWeight()>weightLimit;
    } else {
      unsigned selCnt=cl->selected();
      unsigned maxSelWeight=0;
      for(unsigned i=0;i<selCnt;i++) {
        maxSelWeight=max((*cl)[i]->weight(),maxSelWeight);
      }
      shouldRemove=cl->weight()-(int)maxSelWeight>=weightLimit;
    }

    if(shouldRemove) {
      ASS(cl->store()==Clause::ACTIVE || cl->store()==Clause::REACTIVATED);
      toRemove.push(cl);
    }
  }

#if OUTPUT_LRS_DETAILS
  if(toRemove.isNonEmpty()) {
    cout<<toRemove.size()<<" active deleted\n";
  }
#endif

  while(toRemove.isNonEmpty()) {
    Clause* removed=toRemove.pop();
    ASS(removed->store()==Clause::ACTIVE || removed->store()==Clause::REACTIVATED);

    if(removed->store()!=Clause::REACTIVATED) {
      env.statistics->discardedNonRedundantClauses++;
    }

    remove(removed);
    ASS(removed->store()!=Clause::ACTIVE && removed->store()!=Clause::REACTIVATED);
  }
}

}

