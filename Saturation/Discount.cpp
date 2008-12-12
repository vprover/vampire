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


bool Discount::processInactive(Clause* c)
{
  bool keep;
  ClauseIterator toAdd;
  _fwSimplifier->perform(c,keep,toAdd);
  _unprocessed->addClauses(toAdd);
  return keep;
}

void Discount::activate(Clause* c)
{
  ClauseIterator toAdd;
  ClauseIterator toRemove;
  _bwSimplifier->perform(c,toRemove, toAdd);
  _active->removeClauses(toRemove);
  _unprocessed->addClauses(toAdd);

  _selector->select(c);

  toAdd=_generator->generateClauses(c);
  _unprocessed->addClauses(toAdd);

  _active->add(c);
}

SaturationResult Discount::saturate()
{
  CALL("DiscountSA::saturate");

  for (;;) {
    int counter=0;
    while (! _unprocessed->isEmpty()) {
      Clause* c = _unprocessed->pop();

      if (c->isEmpty()) {
    	return SaturationResult(Statistics::REFUTATION, c);
      }
      if(!processInactive(c)) {
	c->setStore(Clause::NONE);
	continue;
      }
      _passive->add(c);

      if(++counter==50) {
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
    if(!processInactive(c)) {
	c->setStore(Clause::NONE);
	continue;
    }
    activate(c);

    if (env.timeLimitReached()) {
      return SaturationResult(Statistics::TIME_LIMIT);
    }
  }
}
