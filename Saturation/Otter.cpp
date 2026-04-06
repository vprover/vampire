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
 * @file Otter.cpp
 * Implements class Otter.
 */

#include "Kernel/Clause.hpp"
#include "Shell/Options.hpp"

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
  if(cl->store()==Clause::ACTIVE) {
    _simplCont.remove(cl);
  }

  SaturationAlgorithm::onActiveRemoved(cl);
}

void Otter::onPassiveAdded(Clause* cl)
{
  SaturationAlgorithm::onPassiveAdded(cl);

  if(cl->store()==Clause::PASSIVE) {
    _simplCont.add(cl);
  }
}

void Otter::onPassiveRemoved(Clause* cl)
{
  if(cl->store()==Clause::PASSIVE) {
    _simplCont.remove(cl);
  }

  SaturationAlgorithm::onPassiveRemoved(cl);
}

void Otter::onClauseRetained(Clause* cl)
{
  SaturationAlgorithm::onClauseRetained(cl);

  backwardSimplify(cl);
}

void Otter::onSOSClauseAdded(Clause* cl)
{
  ASS(cl);
  ASS_EQ(cl->store(), Clause::ACTIVE);

  SaturationAlgorithm::onSOSClauseAdded(cl);

  _simplCont.add(cl);
}

void Otter::beforeSelectedRemoved(Clause* cl)
{
  ASS_EQ(cl->store(), Clause::SELECTED);
  _simplCont.remove(cl);
}

}
