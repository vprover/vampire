
/*
 * File Discount.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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

