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

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;



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

//  unsigned currTime=env.timer->elapsedMilliseconds();

  static unsigned cnt=0;
//  static unsigned lastCheck=currTime;
  cnt++;
//  if(cnt==500 || currTime>lastCheck+500) {
  if(cnt==500) {
//  if(currTime>lastCheck+500) {
//  if(currTime>lastCheck+5) {
//  if(currTime>lastCheck+50) {
    cnt=0;
//    lastCheck=currTime;
    return true;
  }
  return false;
}

long LRS::estimatedReachableCount()
{
  CALL("LRS::estimatedReachableCount");

  unsigned processed=env.statistics->activeClauses;
  int currTime=env.timer->elapsedMilliseconds();
  int timeSpent=currTime-_startTime;
  //the result is in miliseconds, as env.options->lrsFirstTimeCheck() is in percents.
  int firstCheck=env.options->lrsFirstTimeCheck()*env.options->timeLimitInDeciseconds();
//  int timeSpent=currTime;

  if(timeSpent<firstCheck ) {
    return -1;
  }

  long timeLeft;
  if(env.options->simulatedTimeLimit()) {
    timeLeft=env.options->simulatedTimeLimit()*100 - currTime;
  } else {
    timeLeft=env.options->timeLimitInDeciseconds()*100 - currTime;
  }
  if(timeLeft<=0 || processed<=10) {
    return -1;
  }
  return (processed*timeLeft)/timeSpent;
}


SaturationResult LRS::saturate()
{
  CALL("LRS::saturate");

  handleSaturationStart();

  for (;;) {
    while (! _unprocessed->isEmpty()) {
      Clause* c = _unprocessed->pop();

      if (isRefutation(c)) {
    	return SaturationResult(Statistics::REFUTATION, c);
      }
      if(forwardSimplify(c)) {
	backwardSimplify(c);
	addToPassive(c);
	_simplCont.add(c);
      } else {
	ASS_EQ(c->store(), Clause::UNPROCESSED);
	c->setStore(Clause::NONE);
      }

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
//    if(env.timer->elapsedMilliseconds()>15000) {
//      cout<<(*c)<<endl;
//    }
  }
}

}
