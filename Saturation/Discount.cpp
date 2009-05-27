/**
 * @file Discount.cpp
 * Implements class Discount.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/LiteralSelector.hpp"
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
    int counter=0;
    while (! _unprocessed->isEmpty()) {
      Clause* c = _unprocessed->pop();

      if(isRefutation(c)) {
    	return SaturationResult(Statistics::REFUTATION, c);
      }
      if(forwardSimplify(c)) {
	addToPassive(c);
      } else {
	ASS_EQ(c->store(), Clause::UNPROCESSED);
	c->setStore(Clause::NONE);
      }

      if(++counter==100) {
	counter=0;
	if (env.timeLimitReached()) {
	  return SaturationResult(Statistics::TIME_LIMIT);
	}
      }
    }

    if(env.timeLimitReached()) {
      return SaturationResult(Statistics::TIME_LIMIT);
    }
    if(_passive->isEmpty()) {
      return SaturationResult(Statistics::SATISFIABLE);
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
    activate(cl);

    if(env.timeLimitReached()) {
      return SaturationResult(Statistics::TIME_LIMIT);
    }
  }
}
