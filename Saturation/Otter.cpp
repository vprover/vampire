/**
 * @file Otter.cpp
 * Implements class Otter.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/LiteralSelector.hpp"
#include "../Shell/Options.hpp"
#include "../Shell/Statistics.hpp"

#include "Otter.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;

Otter::Otter(PassiveClauseContainerSP passiveContainer, LiteralSelectorSP selector)
  : SaturationAlgorithm(passiveContainer,selector)
{
}

ClauseContainer* Otter::getSimplificationClauseContainer()
{
  return &_simplCont;
}

ClauseContainer* Otter::getGenerationClauseContainer()
{
  return _active;
}

void Otter::onActiveRemoved(Clause* cl)
{
  CALL("Otter::onActiveRemoved");

  if(cl->store()==Clause::ACTIVE) {
    _simplCont.remove(cl);
  }

  SaturationAlgorithm::onActiveRemoved(cl);
}

void Otter::onPassiveAdded(Clause* cl)
{
  CALL("Otter::onPassiveAdded");

  if(cl->store()==Clause::PASSIVE) {
    _simplCont.add(cl);
  }
}

void Otter::onPassiveRemoved(Clause* cl)
{
  CALL("Otter::onPassiveRemoved");

  if(cl->store()==Clause::PASSIVE) {
    _simplCont.remove(cl);
  }

  SaturationAlgorithm::onPassiveRemoved(cl);
}

void Otter::onClauseRetained(Clause* cl)
{
  CALL("Otter::onClauseRetained");

  backwardSimplify(cl);
}

void Otter::onSOSClauseAdded(Clause* cl)
{
  CALL("Otter::onSOSClauseAdded");
  ASS(cl);
  ASS_EQ(cl->store(), Clause::ACTIVE);

  _simplCont.add(cl);
}

void Otter::handleUnsuccessfulActivation(Clause* c)
{
  CALL("Otter::handleUnsuccessfulActivation");

  if(c->store()==Clause::REACTIVATED) {
    c->setStore(Clause::ACTIVE);
  }
  else {
    //reactivated clauses should always get activated
    ASS_EQ(c->store(), Clause::PASSIVE);
    _simplCont.remove(c);
    c->setStore(Clause::NONE);
  }
}

SaturationResult Otter::doSaturation()
{
  CALL("Otter::doSaturation");

  for (;;) {
    newClausesToUnprocessed();

    while (! _unprocessed->isEmpty()) {
      Clause* c = _unprocessed->pop();
      ASS(!isRefutation(c));

      if(forwardSimplify(c)) {
	onClauseRetained(c);
	addToPassive(c);
	ASS_EQ(c->store(), Clause::PASSIVE);
      }
      else {
	ASS_EQ(c->store(), Clause::UNPROCESSED);
	c->setStore(Clause::NONE);
      }

      newClausesToUnprocessed();

      if(env.timeLimitReached()) {
	return SaturationResult(Statistics::TIME_LIMIT);
      }
    }
    onAllProcessed();
    if(!clausesFlushed()) {
      //there were some new clauses added, so let's process them
      continue;
    }

    if (_passive->isEmpty()) {
      if(env.options->complete()) {
	return SaturationResult(Statistics::SATISFIABLE);
      } else {
	return SaturationResult(Statistics::REFUTATION_NOT_FOUND);
      }
    }

    Clause* c = _passive->popSelected();

    bool isActivated=activate(c);
    if(!isActivated) {
      handleUnsuccessfulActivation(c);
    }

    if(env.timeLimitReached()) {
      return SaturationResult(Statistics::TIME_LIMIT);
    }
  }
}
