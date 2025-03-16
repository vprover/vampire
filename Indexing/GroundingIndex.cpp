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
 * @file GroundingIndex.cpp
 * Implements class GroundingIndex.
 */

#include "GroundingIndex.hpp"

#include "Kernel/Grounder.hpp"
#include "Shell/Options.hpp"
#include "SAT/MinisatInterfacing.hpp"
#include "SAT/CadicalInterfacing.hpp"

namespace Indexing
{

using namespace std;

GroundingIndex::GroundingIndex(const Options& opt)
{
  if(opt.satSolver() == Options::SatSolver::MINISAT)
    _solver = new MinisatInterfacing(opt, true);
  else
    _solver = new CadicalInterfacing(opt, true);

  _grounder = new Kernel::GlobalSubsumptionGrounder(*_solver);
}
}
