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
#include "SAT/Z3Interfacing.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Indexing
{

GroundingIndex::GroundingIndex(const Options& opt)
{
  CALL("GroundingIndex::GroundingIndex");

  SAT2FO* sat2fo = 0;

  switch(opt.satSolver()){
    case Options::SatSolver::VAMPIRE:
    	_solver = new TWLSolver(opt,true);
    	break;
    case Options::SatSolver::LINGELING:
      _solver = new LingelingInterfacing(opt,true);
    	break;
#if VZ3
    case Options::SatSolver::Z3:
     sat2fo = new SAT2FO();
     _solver = new Z3Interfacing(opt,*sat2fo);
     break;
#endif
    case Options::SatSolver::MINISAT:
      _solver = new MinisatInterfacing(opt,true);
    	break;
    default:
      ASSERTION_VIOLATION_REP(opt.satSolver());
  }
  
  _grounder = new GlobalSubsumptionGrounder(_solver.ptr());
  _grounder->setSAT2FO(sat2fo);
}

void GroundingIndex::handleClause(Clause* c, bool adding)
{
  CALL("GroundingIndex::handleClause");

  //We are adding clauses into the index when performing the subsumption check
}

}
