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

#include "Lib/Environment.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/LiteralSelector.hpp"
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

void Otter::activeOrDelayedClauseAdded(Clause* cl)
{
}

void Otter::onPassiveAdded(Clause* cl)
{
  SaturationAlgorithm::onPassiveAdded(cl);
  _simplCont.add(cl);
}

void Otter::onPassiveRemoved(Clause* cl)
{
  _simplCont.remove(cl);
  SaturationAlgorithm::onPassiveRemoved(cl);
}

void Otter::onClauseRetained(Clause* cl)
{
  SaturationAlgorithm::onClauseRetained(cl);

  backwardSimplify(cl);
}

void Otter::beforeSelectedRemoved(Clause* cl)
{
  ASS_EQ(cl->store(), Clause::SELECTED);
  _simplCont.remove(cl);
}

}
