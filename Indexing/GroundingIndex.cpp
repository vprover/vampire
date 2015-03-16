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
#include "SAT/LingelingInterfacing.hpp"
#include "SAT/MinisatInterfacing.hpp"
#include "SAT/BufferedSolver.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Indexing
{

GroundingIndex::GroundingIndex(Grounder* gnd, const Options& opt)
 : _grounder(gnd)
{
  CALL("GroundingIndex::GroundingIndex");

  switch(opt.satSolver()){
    case Options::SatSolver::VAMPIRE:
    case Options::SatSolver::BUFFERED_VAMPIRE: // Buffering ignored for global subsumption
    	_solver = new TWLSolver(opt,true);
    	break;
    case Options::SatSolver::LINGELING:
    case Options::SatSolver::BUFFERED_LINGELING: // Buffering ignored for global subsumption
      _solver = new LingelingInterfacing(opt,true);
    	break;
    case Options::SatSolver::MINISAT:
    case Options::SatSolver::BUFFERED_MINISAT: // Buffering ignored for global subsumption
      _solver = new MinisatInterfacing(opt,true);
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
