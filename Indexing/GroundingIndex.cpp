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
    case Options::VAMPIRE:
    	_solver = new TWLSolver(opt,true);
    	break;
    case Options::BUFFERED_VAMPIRE:
    	_solver = new BufferedSolver(new TWLSolver(opt,true));
    	break;
    case Options::BUFFERED_LINGELING:
    	_solver = new BufferedSolver(new LingelingInterfacing(opt, true));
    	break;
    case Options::LINGELING:
      _solver = new LingelingInterfacing(opt,true);
      break;
    case Options::BUFFERED_MINISAT:
    	_solver = new BufferedSolver(new MinisatInterfacing(opt, true));
    	break;
    case Options::MINISAT:
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
