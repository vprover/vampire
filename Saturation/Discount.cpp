/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Discount.cpp
 * Implements class Discount.
 */

#include "Lib/Environment.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/RewritingData.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Inferences/ReducibilityChecker.hpp"

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
  ASS(cl->store()==Clause::SELECTED);

  if (!forwardSimplify(cl)) {
    cl->setStore(Clause::NONE);
    return false;
  }
  if (_checker && _checker->checkInferenceLazy(cl)) {
    cl->setStore(Clause::NONE);
    env.statistics->redundantSuperposition++;
    return false;
  }
  // if (cl->rewritingData()) {
  //   delete cl->rewritingData();
  //   cl->setRewritingData(nullptr);
  // }
  backwardSimplify(cl);
  return true;
}

