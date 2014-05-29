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

  //TODO - why is the test for if_active necessary?
  bool is_active = (cl->store()==Clause::ACTIVE) || (cl->isFrozen() && cl->prevStore()==Clause::ACTIVE);

  if(is_active && cl->in_simplifying()) {
    _simplCont.remove(cl);
    cl->toggle_in_simplifying();
  }
  else{
   if(cl->in_simplifying()){
     cout << "cl in simplifying not removed" << endl;
   }
  }

  SaturationAlgorithm::onActiveRemoved(cl);

  ASS(!cl->in_simplifying());
  ASS(!cl->in_generating());
}

void Otter::onPassiveAdded(Clause* cl)
{
  CALL("Otter::onPassiveAdded");

  SaturationAlgorithm::onPassiveAdded(cl);

  //TODO - can cl not be PASSIVE for any reason?
  if(cl->store()==Clause::PASSIVE && !cl->in_simplifying()) {
    _simplCont.add(cl);
    cl->toggle_in_simplifying();
  }
  ASS(cl->in_simplifying());
}

void Otter::onPassiveRemoved(Clause* cl)
{
  CALL("Otter::onPassiveRemoved");

  bool is_passive = cl->store()==Clause::PASSIVE || (cl->isFrozen() && cl->prevStore()==Clause::PASSIVE);

  if(is_passive) {
    ASS(cl->in_simplifying());
    _simplCont.remove(cl);
    cl->toggle_in_simplifying();
    ASS(!cl->in_simplifying());
  }
  else{
    // clause is active and we keep it in simplCont
    ASS_EQ(cl->store(),Clause::ACTIVE);
  }

  SaturationAlgorithm::onPassiveRemoved(cl);
}

void Otter::onClauseRetained(Clause* cl)
{
  CALL("Otter::onClauseRetained");

  ASS_EQ(cl->store(), Clause::PASSIVE);
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

  ASS_EQ(c->store(), Clause::SELECTED);
  ASS(c->in_simplifying()); // I assume as we're removing it it should be added
  _simplCont.remove(c);
  c->toggle_in_simplifying();
  c->setStore(Clause::NONE);
}

}
