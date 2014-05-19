/**
 * @file Otter.cpp
 * Implements class Otter.
 */

#include "Lib/Environment.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Otter.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;

Otter::Otter(Problem& prb, const Options& opt)
  : SaturationAlgorithm(prb, opt)
{
}

ClauseContainer* Otter::getSimplifyingClauseContainer()
{
  return &_simplCont;
}

void Otter::onActiveRemoved(Clause* cl)
{
  CALL("Otter::onActiveRemoved");

  if(cl->store()==Clause::ACTIVE && cl->in_simplifying()) {
    _simplCont.remove(cl);
    cl->toggle_in_simplifying();
  }

  SaturationAlgorithm::onActiveRemoved(cl);

  ASS(!cl->in_simplifying());
  ASS(!cl->in_generating());
}

void Otter::onPassiveAdded(Clause* cl)
{
  CALL("Otter::onPassiveAdded");

  SaturationAlgorithm::onPassiveAdded(cl);

  if(cl->store()==Clause::PASSIVE && !cl->in_simplifying()) {
    _simplCont.add(cl);
    cl->toggle_in_simplifying();
  }
  ASS(cl->in_simplifying());
}

void Otter::onPassiveRemoved(Clause* cl)
{
  CALL("Otter::onPassiveRemoved");

  if(cl->store()==Clause::PASSIVE) {
    ASS(cl->in_simplifying());
    _simplCont.remove(cl);
    cl->toggle_in_simplifying();
    ASS(!cl->in_simplifying());
  }// else clause is active and we keep it in simplCont

  SaturationAlgorithm::onPassiveRemoved(cl);
}

void Otter::onClauseRetained(Clause* cl)
{
  CALL("Otter::onClauseRetained");

  SaturationAlgorithm::onClauseRetained(cl);

  backwardSimplify(cl);
}

void Otter::onSOSClauseAdded(Clause* cl)
{
  CALL("Otter::onSOSClauseAdded");
  ASS(cl);
  ASS_EQ(cl->store(), Clause::ACTIVE);

  SaturationAlgorithm::onSOSClauseAdded(cl);

  ASS(!cl->in_simplifying());
  cl->toggle_in_simplifying();
  _simplCont.add(cl);
}

void Otter::handleUnsuccessfulActivation(Clause* c)
{
  CALL("Otter::handleUnsuccessfulActivation");

  //TODO update in_simplifying and in_generating appropriately
  ASS_EQ(c->store(), Clause::SELECTED);
  _simplCont.remove(c);
  c->setStore(Clause::NONE);
}

}
