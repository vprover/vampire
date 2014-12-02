/**
 * @file Discount.cpp
 * Implements class Discount.
 */

#include "Discount.hpp"

#include "Kernel/Clause.hpp"

namespace Saturation{

using Kernel::Clause;
using Kernel::ClauseContainer;

ClauseContainer* Discount::getSimplifyingClauseContainer()
{
  return _active;
}

bool Discount::handleClauseBeforeActivation(Clause* cl)
{
  CALL("Discount::handleClauseBeforeActivation");
  ASS(cl->store()==Clause::SELECTED);

  if (!forwardSimplify(cl)) {
    cl->setStore(Clause::NONE);
    return false;
  }
  backwardSimplify(cl);
  return true;
}

}//namespace Saturation
