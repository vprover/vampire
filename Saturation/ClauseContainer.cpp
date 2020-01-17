
/*
 * File ClauseContainer.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file ClauseContainer.cpp
 * Implementing ClauseContainer and its descendants.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Stack.hpp"
#include "Kernel/Clause.hpp"
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

void ClauseContainer::addClauses(ClauseIterator cit)
{
  while (cit.hasNext()) {
    add(cit.next());
  }
}


/////////////////   RandomAccessClauseContainer   //////////////////////

void RandomAccessClauseContainer::removeClauses(ClauseIterator cit)
{
  while (cit.hasNext()) {
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
      this, &RandomAccessClauseContainer::onLimitsUpdated);
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


/////////////////   UnprocessedClauseContainer   //////////////////////

UnprocessedClauseContainer::~UnprocessedClauseContainer()
{
  CALL("UnprocessedClauseContainer::~UnprocessedClauseContainer");

  while (!_data.isEmpty()) {
    Clause* cl=_data.pop_back();
    ASS_EQ(cl->store(), Clause::UNPROCESSED);
    cl->setStore(Clause::NONE);
  }
}

void UnprocessedClauseContainer::add(Clause* c)
{
  CALL("UnprocessedClauseContainer::add");

  _data.push_back(c);
  addedEvent.fire(c);
}

Clause* UnprocessedClauseContainer::pop()
{
  CALL("UnprocessedClauseContainer::pop");

  Clause* res=_data.pop_back();
  selectedEvent.fire(res);
  return res;
}



/////////////////   ActiveClauseContainer   //////////////////////

void ActiveClauseContainer::add(Clause* c)
{
  CALL("ActiveClauseContainer::add");

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
  ASS(c->store()==Clause::ACTIVE);

  _size--;
  removedEvent.fire(c);
} // Active::ClauseContainer::remove

void ActiveClauseContainer::onLimitsUpdated(LimitsChangeType change)
{
  CALL("ActiveClauseContainer::onLimitsUpdated");

  if (change==LIMITS_LOOSENED) {
    return;
  }
  LiteralIndexingStructure* gis=getSaturationAlgorithm()->getIndexManager()
      ->getGeneratingLiteralIndexingStructure();
  if (!gis) {
    return;
  }
  Limits* limits=getSaturationAlgorithm()->getLimits();

  ASS(limits);
  if (!limits->ageLimited() || !limits->weightLimited()) {
    return;
  }

  unsigned ageLimit=limits->ageLimit();

  static DHSet<Clause*> checked;
  static Stack<Clause*> toRemove(64);
  checked.reset();
  toRemove.reset();

  SLQueryResultIterator rit=gis->getAll();
  while (rit.hasNext()) {
    Clause* cl=rit.next().clause;
    ASS(cl);
    if (cl->age()<ageLimit || checked.contains(cl)) {
      continue;
    }
    checked.insert(cl);

    bool shouldRemove;
    if (!limits->fulfilsAgeLimit(cl)) {
      shouldRemove=!limits->fulfilsWeightLimit(cl);
    }
    else {
      unsigned selCnt=cl->numSelected();
      unsigned maxSelWeight=0;
      for(unsigned i=0;i<selCnt;i++) {
        maxSelWeight=max((*cl)[i]->weight(),maxSelWeight);
      }
      unsigned weightLowerBound = cl->weight() - maxSelWeight; // heuristic: we assume that at most one literal will be removed from the clause.
      unsigned numeralWeight = 0; // heuristic: we don't know the numeral weight of the child, and conservatively assume that it is 0.
      bool derivedFromGoal = true; // heuristic: we have to cover the case where the child has another parent which is a goal-clause. We conservatively assume that the result is a goal-clause.
      shouldRemove = !limits->fulfilsWeightLimit(weightLowerBound, numeralWeight, derivedFromGoal);
    }

    if (shouldRemove) {
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

    RSTAT_CTR_INC("clauses discarded from active on weight limit update");
    env.statistics->discardedNonRedundantClauses++;

    remove(removed);
    ASS_NEQ(removed->store(), Clause::ACTIVE);
  }
}

}

