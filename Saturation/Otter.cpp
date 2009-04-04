/**
 * @file Otter.cpp
 * Implements class Otter.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/LiteralSelector.hpp"
#include "../Shell/Statistics.hpp"

#include "Otter.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;


ClauseContainer* Otter::getSimplificationClauseContainer()
{
  return &_simplCont;
}

ClauseContainer* Otter::getGenerationClauseContainer()
{
  return _active;
}


bool Otter::processUnprocessed(Clause* c)
{
  CALL("Otter::processUnprocessed");
  bool keep;
  ClauseIterator toAdd;
  _fwSimplifier->perform(c,keep,toAdd);
  _unprocessed->addClauses(toAdd);

  return keep;
}

void Otter::backwardSimplify(Clause* c)
{
  ClauseIterator toAdd;
  ClauseIterator toRemove;
  _bwSimplifier->perform(c,toRemove,toAdd);
  _unprocessed->addClauses(toAdd);
  while(toRemove.hasNext()) {
    Clause* redundant=toRemove.next();
    _simplCont.remove(redundant);
    switch(redundant->store()) {
    case Clause::PASSIVE:
      _passive->remove(redundant);
      break;
    case Clause::ACTIVE:
      _active->remove(redundant);
      break;
    default:
      ASSERTION_VIOLATION;
    }
  }
}

void Otter::activate(Clause* c)
{
  CALL("Otter::activate");

  _selector->select(c);

  _active->add(c);

  ClauseIterator toAdd=_generator->generateClauses(c);
  _unprocessed->addClauses(toAdd);

}

SaturationResult Otter::saturate()
{
  CALL("Otter::saturate");

  for (;;) {
    while (! _unprocessed->isEmpty()) {
      Clause* c = _unprocessed->pop();

      if (c->isEmpty()) {
    	return SaturationResult(Statistics::REFUTATION, c);
      }
      if(processUnprocessed(c)) {
	backwardSimplify(c);
	_passive->add(c);
	_simplCont.add(c);
      } else {
	c->setStore(Clause::NONE);
      }

      if (env.timeLimitReached()) {
	return SaturationResult(Statistics::TIME_LIMIT);
      }
    }

    if (_passive->isEmpty()) {
      return SaturationResult(Statistics::SATISFIABLE);
    }

    Clause* c = _passive->popSelected();
    activate(c);
  }
}
