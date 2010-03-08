/**
 * @file BDDMarkingSubsumption.cpp
 * Implements class BDDMarkingSubsumption.
 */

#include <math.h>

#include "../Lib/DHSet.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/SharedSet.hpp"
#include "../Lib/Stack.hpp"

#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Shell/Statistics.hpp"

#include "BDDMarkingSubsumption.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

void BDDMarkingSubsumption::init(SaturationAlgorithm *sa)
{
  CALL("BDDMarkingSubsumption::init");

  _sa=sa;
}

/**
 * Return true if the clause @b cl is subsumed
 *
 * If @b cl is subsumed, also update the statistics.
 */
bool BDDMarkingSubsumption::subsumed(Clause* cl)
{
  CALL("BDDMarkingSubsumption::subsumed");

  bool res=BDD::instance()->isRefuted(cl->prop());
  if(res) {
    env.statistics->subsumedByMarking++;
  }
  return res;
}

void BDDMarkingSubsumption::onNewPropositionalClause(Clause* cl)
{
  CALL("BDDMarkingSubsumption::onNewPropositionalClause");

  BDD* bdd=BDD::instance();

  if(cl->isEmpty() && !bdd->isFalse(cl->prop())) {
    ASS(cl->splits()->isEmpty());

    bdd->markRefuted(cl->prop());
  }
}

/**
 * To be called when there are no new or unprocessed clauses left
 *
 * This function from time to time goes through all passive and active
 * clauses and removes those that are subsumed.
 */
void BDDMarkingSubsumption::onAllProcessed()
{
  CALL("BDDMarkingSubsumption::onAllProcessed");

  static Stack<Clause*> toRemove(64);
  static DHSet<Clause*> checked;
  static BDD* bdd=BDD::instance();

  static int counter1=0;
  counter1++;
  if(counter1>sqrt((float)_sa->activeClauseCount())) {
    counter1=0;

    TimeCounter tc(TC_BDD_MARKING_SUBSUMPTION);

    //check active clauses
    checked.reset();
    ClauseIterator rit=_sa->activeClauses();
    while(rit.hasNext()) {
	Clause* cl=rit.next();
	if(checked.find(cl)) {
	  continue;
	}
	checked.insert(cl);
	if(bdd->isRefuted(cl->prop())) {
	  toRemove.push(cl);
	}
    }
  }

  static int counter2=0;
  counter2++;
  if(counter2>sqrt((float)_sa->passiveClauseCount())) {
    counter2=0;

    TimeCounter tc(TC_BDD_MARKING_SUBSUMPTION);

    //check passive clauses
    checked.reset();
    ClauseIterator cit=_sa->passiveClauses();
    while(cit.hasNext()) {
	Clause* cl=cit.next();
	if(cl->store()!=Clause::PASSIVE || checked.find(cl)) {
	  continue;
	}
	checked.insert(cl);
	if(bdd->isRefuted(cl->prop())) {
	  toRemove.push(cl);
	}
    }
  }

  if(toRemove.isNonEmpty()) {
    TimeCounter tc(TC_BDD_MARKING_SUBSUMPTION);

    while(toRemove.isNonEmpty()) {
	Clause* cl=toRemove.pop();

	cl->setProp(bdd->getTrue());
	_sa->removeActiveOrPassiveClause(cl);
	env.statistics->subsumedByMarking++;
    }
  }

}

}



