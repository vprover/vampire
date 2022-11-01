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

#include "Lib/SharedSet.hpp"

#include "Kernel/Grounder.hpp"
#include "Kernel/Inference.hpp"

#include "Shell/Options.hpp"

#include "SAT/MinisatInterfacing.hpp"
#include "SAT/BufferedSolver.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Indexing
{

GroundingIndex::GroundingIndex(const Options& opt)
{
  CALL("GroundingIndex::GroundingIndex");

  switch(opt.satSolver()){
#if VZ3
    case Options::SatSolver::Z3:
      // TODO still some issues to resolve here when running with AVATAR
      //_solver = new Z3Interfacing(opt,_sat2fo, /* unsat core */ false,"");
      //_grounder = new GlobalSubsumptionGrounder(_solver.ptr(), &_sat2fo);
      //break;    
#endif
    case Options::SatSolver::MINISAT:
      _solver = new MinisatInterfacing(opt,true);
      _grounder = new GlobalSubsumptionGrounder(_solver.ptr());
      break;
    default:
      ASSERTION_VIOLATION_REP(opt.satSolver());
  }
}

void GroundingIndex::handleClause(Clause* c, bool adding)
{
  CALL("GroundingIndex::handleClause");

  //We are adding clauses into the index when performing the subsumption check
}

}
