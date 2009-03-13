/**
 * @file LRS.cpp
 * Implements class LRS.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Timer.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/LiteralSelector.hpp"
#include "../Shell/Statistics.hpp"
#include "../Shell/Options.hpp"

#include "LRS.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;


ClauseContainer* LRS::getSimplificationClauseContainer()
{
  return &_simplCont;
}

ClauseContainer* LRS::getGenerationClauseContainer()
{
  return _active;
}

long LRS::getReachableCountEstimate()
{
  unsigned processed=env.statistics->activeClauses;
  unsigned timeSpent=env.timer->elapsedMilliseconds();
  long timeLeft=env.options->timeLimitInDeciseconds()*100 - timeSpent;
  if(timeLeft<0) {
    return 0;
  }
  return (processed*timeLeft)/timeSpent;
}


bool LRS::processUnprocessed(Clause* c)
{
  CALL("LRS::processUnprocessed");
  bool keep;
  ClauseIterator toAdd;
  _fwSimplifier->perform(c,keep,toAdd);
  _unprocessed->addClauses(toAdd);

  return keep;
}

void LRS::backwardSimplify(Clause* c)
{
  ClauseIterator toAdd;
  ClauseIterator toRemove;
  _bwSimplifier->perform(c,toRemove,toAdd);
  _unprocessed->addClauses(toAdd);
  while(toRemove.hasNext()) {
    Clause* redundant=toRemove.next();
    _simplCont.remove(redundant);
    if(!_passive->tryRemove(redundant)) {
      _active->remove(redundant);
    }
  }
}

void LRS::activate(Clause* c)
{
  CALL("LRS::activate");

  _selector->select(c);
  ClauseIterator toAdd=_generator->generateClauses(c);
  _unprocessed->addClauses(toAdd);

  _active->add(c);
}

SaturationResult LRS::saturate()
{
  CALL("LRS::saturate");

  for (;;) {
    while (! _unprocessed->isEmpty()) {
      Clause* c = _unprocessed->pop();

      if (c->isEmpty()) {
    	return SaturationResult(Statistics::REFUTATION, c);
      }
      if(!processUnprocessed(c)) {
	c->setStore(Clause::NONE);
	continue;
      }
      backwardSimplify(c);

      _passive->add(c);
      _simplCont.add(c);

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
