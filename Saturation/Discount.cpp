/**
 * @file Discount.cpp
 * Implements class Discount.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/LiteralSelector.hpp"
#include "../Shell/Options.hpp"
#include "../Shell/Statistics.hpp"

#include "Discount.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;


ClauseContainer* Discount::getSimplificationClauseContainer()
{
  return _active;
}

ClauseContainer* Discount::getGenerationClauseContainer()
{
  return _active;
}

SaturationResult Discount::saturate()
{
  CALL("Discount::saturate");

  handleSaturationStart();

  for (;;) {
    newClausesToUnprocessed();

    int counter=0;
    while (! _unprocessed->isEmpty()) {
      Clause* c = _unprocessed->pop();

      if(isRefutation(c)) {
    	return SaturationResult(Statistics::REFUTATION, c);
      }

      bool inPassive=false;
      if(forwardSimplify(c)) {
	inPassive=addToPassive(c);
      }
      ASS(!inPassive || c->store()==Clause::PASSIVE);
      if(!inPassive) {
	ASS_EQ(c->store(), Clause::UNPROCESSED);
	c->setStore(Clause::NONE);
      }

      newClausesToUnprocessed();

      if(++counter==100) {
	counter=0;
	if (env.timeLimitReached()) {
	  return SaturationResult(Statistics::TIME_LIMIT);
	}
      }
    }

    onAllProcessed();
    if(!clausesFlushed()) {
      //there were some new clauses added, so let's process them
      continue;
    }

    if(env.timeLimitReached()) {
      return SaturationResult(Statistics::TIME_LIMIT);
    }
    if(_passive->isEmpty()) {
      if(env.options->complete()) {
	return SaturationResult(Statistics::SATISFIABLE);
      } else {
	return SaturationResult(Statistics::UNKNOWN);
      }
    }

    Clause* cl = _passive->popSelected();
    if(!forwardSimplify(cl)) {
      if(cl->store()==Clause::REACTIVATED) {
	_active->remove(cl);
      }
      cl->setStore(Clause::NONE);
      continue;
    }
    backwardSimplify(cl);

    bool isActivated=activate(cl);
    if(!isActivated) {
      //reactivated clauses should always get activated
      ASS_EQ(cl->store(), Clause::PASSIVE);
      cl->setStore(Clause::NONE);
    }

    if(env.timeLimitReached()) {
      return SaturationResult(Statistics::TIME_LIMIT);
    }
  }
}
