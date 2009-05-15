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

Otter::Otter(PassiveClauseContainerSP passiveContainer, LiteralSelectorSP selector)
  : SaturationAlgorithm(passiveContainer,selector)
{
  _passiveContRemovalSData=_passive->removedEvent.subscribe(
      &_simplCont, &FakeContainer::remove);
  _activeContRemovalSData=_active->removedEvent.subscribe(
      &_simplCont, &FakeContainer::remove);
}

ClauseContainer* Otter::getSimplificationClauseContainer()
{
  return &_simplCont;
}

ClauseContainer* Otter::getGenerationClauseContainer()
{
  return _active;
}

SaturationResult Otter::saturate()
{
  CALL("Otter::saturate");

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
    }

    if (_passive->isEmpty()) {
      return SaturationResult(Statistics::SATISFIABLE);
    }

    Clause* c = _passive->popSelected();
    activate(c);
  }
}
