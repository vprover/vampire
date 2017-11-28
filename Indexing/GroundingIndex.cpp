
/*
 * File GroundingIndex.cpp.
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
 * @file GroundingIndex.cpp
 * Implements class GroundingIndex.
 */

#include "GroundingIndex.hpp"

#include "Lib/SharedSet.hpp"

#include "Kernel/Grounder.hpp"
#include "Kernel/Inference.hpp"

#include "Shell/Options.hpp"

#include "SAT/TWLSolver.hpp"
#include "SAT/MinisatInterfacing.hpp"
#include "SAT/BufferedSolver.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Indexing
{

GroundingIndex::GroundingIndex(const Options& opt)
{
  CALL("GroundingIndex::GroundingIndex");

  switch(opt.satSolver()){
    case Options::SatSolver::VAMPIRE:
    	_solver = new TWLSolver(opt,true);
    	break;
#if VZ3
    case Options::SatSolver::Z3:
      //cout << "Warning, Z3 not curently used for Global Subsumption" << endl; 
#endif
    case Options::SatSolver::MINISAT:
      _solver = new MinisatInterfacing(opt,true);
    	break;
    default:
      ASSERTION_VIOLATION_REP(opt.satSolver());
  }
  
  _grounder = new GlobalSubsumptionGrounder(_solver.ptr());
}

void GroundingIndex::handleClause(Clause* c, bool adding)
{
  CALL("GroundingIndex::handleClause");

  //We are adding clauses into the index when performing the subsumption check
}

}
