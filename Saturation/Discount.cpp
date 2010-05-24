/**
 * @file Discount.cpp
 * Implements class Discount.
 */

#include "Lib/Environment.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

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

bool Discount::handleClauseBeforeActivation(Clause* cl)
{
  CALL("Discount::handleClauseBeforeActivation");
  ASS(cl->store()==Clause::SELECTED || cl->store()==Clause::SELECTED_REACTIVATED);

  if(!forwardSimplify(cl)) {
    if(cl->store()==Clause::SELECTED_REACTIVATED) {
	_active->remove(cl);
    }
    cl->setStore(Clause::NONE);
    return false;
  }
  backwardSimplify(cl);
  return true;
}

