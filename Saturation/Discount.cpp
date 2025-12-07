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

#include "Kernel/Clause.hpp"

#include "Discount.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;

bool Discount::handleClauseBeforeActivation(Clause* cl)
{
  ASS_EQ(cl->store(), Clause::SELECTED);

  if (!forwardSimplify(cl)) {
    cl->setStore(Clause::NONE);
    return false;
  }
  backwardSimplify(cl);
  return true;
}

