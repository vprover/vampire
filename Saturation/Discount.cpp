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

  for (;;) {
    int counter=0;
    while (! _unprocessed->isEmpty()) {
      Clause* c = _unprocessed->pop();

      if (c->isEmpty()) {
    	return SaturationResult(Statistics::REFUTATION, c);
      }
      if(forwardSimplify(c)) {
	_passive->add(c);
      } else {
	c->setStore(Clause::NONE);
      }

      if(++counter==100) {
	counter=0;
	if (env.timeLimitReached()) {
	  return SaturationResult(Statistics::TIME_LIMIT);
	}
      }
    }

    if (env.timeLimitReached()) {
      return SaturationResult(Statistics::TIME_LIMIT);
    }
    if (_passive->isEmpty()) {
      return SaturationResult(Statistics::SATISFIABLE);
    }

    Clause* c = _passive->popSelected();
    if(!forwardSimplify(c)) {
	c->setStore(Clause::NONE);
	continue;
    }
    backwardSimplify(c);
    activate(c);

    if (env.timeLimitReached()) {
      return SaturationResult(Statistics::TIME_LIMIT);
    }
  }
}
