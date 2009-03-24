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


LRS::LRS(PassiveClauseContainerSP passiveContainer, LiteralSelectorSP selector)
  : SaturationAlgorithm(passiveContainer,selector)
{
  _passiveContRemovalSData=_passive->removedEvent.subscribe(
      &_simplCont, &FakeContainer::remove);
  _activeContRemovalSData=_active->removedEvent.subscribe(
      &_simplCont, &FakeContainer::remove);

}

LRS::~LRS()
{
  _passiveContRemovalSData->unsubscribe();
  _activeContRemovalSData->unsubscribe();
}

ClauseContainer* LRS::getSimplificationClauseContainer()
{
  return &_simplCont;
}

ClauseContainer* LRS::getGenerationClauseContainer()
{
  return _active;
}

bool LRS::shouldUpdateLimits()
{
  CALL("LRS::shouldUpdateLimits");

  unsigned currTime=env.timer->elapsedMilliseconds();

//  static unsigned cnt=0;
  static unsigned lastCheck=currTime;
//  cnt++;
//  if(cnt==500 || currTime>lastCheck+500) {
  if(currTime>lastCheck+500) {
//    cnt=0;
    lastCheck=currTime;
    return true;
  }
  return false;
}

long LRS::estimatedReachableCount()
{
  CALL("LRS::estimatedReachableCount");

  unsigned processed=max(env.statistics->activeClauses,10u);
  int currTime=env.timer->elapsedMilliseconds();
  int timeSpent=currTime-_startTime;

  if(timeSpent<100) {
    return -1;
  }

  long timeLeft=env.options->timeLimitInDeciseconds()*100 - currTime;
  if(timeLeft<=0) {
    return -1;
  }
  return (processed*timeLeft)/timeSpent;
}


bool LRS::processUnprocessed(Clause* cl)
{
  CALL("LRS::processUnprocessed");

  if(!getLimits()->fulfillsLimits(cl)) {
    return false;
  }

  bool keep;
  ClauseIterator toAdd;
  _fwSimplifier->perform(cl,keep,toAdd);
  _unprocessed->addClauses(toAdd);
  return keep;
}

void LRS::backwardSimplify(Clause* c)
{
  CALL("LRS::backwardSimplify");

  ClauseIterator toAdd;
  ClauseIterator toRemove;
  _bwSimplifier->perform(c,toRemove,toAdd);
  _unprocessed->addClauses(toAdd);
  while(toRemove.hasNext()) {
    Clause* redundant=toRemove.next();
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

  _startTime=env.timer->elapsedMilliseconds();

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
      if(shouldUpdateLimits()) {
        long estimatedReachable=estimatedReachableCount();
        if(estimatedReachable>=0) {
  	_passive->updateLimits(estimatedReachable);
        }
      }
    }

    if (_passive->isEmpty()) {
      return SaturationResult(Statistics::UNKNOWN);
    }

    Clause* c = _passive->popSelected();
    activate(c);
  }
}
