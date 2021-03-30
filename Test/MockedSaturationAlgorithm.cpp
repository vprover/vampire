/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "MockedSaturationAlgorithm.hpp"
#include "Kernel/Clause.hpp"

using namespace Kernel;

namespace Test {

void MockedSaturationAlgorithm::addPassive(Clause* cl)
{
  cl->setStore(Clause::PASSIVE);
  _passive->add(cl);
  // onPassiveAdded(cl);
}

void MockedSaturationAlgorithm::addActive(Clause* cl) 
{
  cl->setStore(Clause::ACTIVE);
  _active->add(cl);
  // onActiveAdded(cl);
}

} // namespace Test
