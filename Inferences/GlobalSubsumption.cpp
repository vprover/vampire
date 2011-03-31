/**
 * @file GlobalSubsumption.cpp
 * Implements class GlobalSubsumption.
 */

#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Grounder.hpp"
#include "Kernel/Inference.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/GroundingIndex.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATSolver.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "GlobalSubsumption.hpp"

#undef LOGGING
#define LOGGING 0

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void GlobalSubsumption::attach(SaturationAlgorithm* salg)
{
  CALL("GlobalSubsumption::attach");
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<GroundingIndex*>(
	  _salg->getIndexManager()->request(GLOBAL_SUBSUMPTION_INDEX) );
}

void GlobalSubsumption::detach()
{
  CALL("GlobalSubsumption::detach");
  _index=0;
  _salg->getIndexManager()->release(GLOBAL_SUBSUMPTION_INDEX);
  ForwardSimplificationEngine::detach();
}

/**
 * Add clause to the SATSolver in the index. Return true iff the
 * resulting set is satisfiable.
 */
bool GlobalSubsumption::addClauseToIndex(Clause* cl)
{
  CALL("GlobalSubsumption::addClauseToIndex");

  SATSolver& solver = _index->getSolver();
  Grounder& grounder = _index->getGrounder();

  ASS_EQ(solver.getStatus(),SATSolver::SATISFIABLE);

  SATClauseIterator sclIt = grounder.ground(cl);
  solver.ensureVarCnt(grounder.satVarCnt());
  solver.addClauses(sclIt, true);

  if(solver.getStatus()==SATSolver::UNSATISFIABLE) {
    return false;
  }
  ASS_EQ(solver.getStatus(),SATSolver::SATISFIABLE);
  return true;
}

void GlobalSubsumption::perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer)
{
  CALL("GlobalSubsumption::perform");

  TimeCounter tc(TC_GLOBAL_SUBSUMPTION);

  if(cl->splits() && cl->splits()->size()!=0) {
    //Since we don't remove clauses, we must ignore clauses with splitting
    //history, because it wouldn't be possible to backtrack them
    return;
  }

  if(cl->prop() && !BDD::instance()->isFalse(cl->prop())) {
    //we don't have clausification of BDDs in the grounder yet
    return;
  }

  if(!addClauseToIndex(cl)) {
    //TODO: extract proofs from SAT solver
    Inference* inf = new Inference1(Inference::GLOBAL_SUBSUMPTION, cl);
    Clause* refutation = Clause::fromIterator(LiteralIterator::getEmpty(), Unit::CONJECTURE, inf);

    env.statistics->globalSubsumption++;
    ALWAYS(simplPerformer->willPerform(0));
    simplPerformer->perform(0, refutation);
    ALWAYS(!simplPerformer->clauseKept());
  }

  static SATLiteralStack slits;
  slits.reset();
  static LiteralStack survivors;
  survivors.reset();

  SATSolver& solver = _index->getSolver();
  Grounder& grounder = _index->getGrounder();

  grounder.groundNonProp(cl, slits);

  bool uprOnly = true;

  unsigned clen = slits.size();
  for(unsigned maskedIdx = 0; maskedIdx<clen; maskedIdx++) {
    for(unsigned i = 0; i<clen; i++) {
      if(i==maskedIdx) {
	continue;
      }
      solver.addAssumption(slits[i].opposite(), uprOnly);

      if(solver.getStatus()==SATSolver::UNSATISFIABLE) {
	for(unsigned j=0; j<=i; j++) {
	  if(j==maskedIdx) {
	    continue;
	  }
	  survivors.push((*cl)[j]);
	}

	//TODO: extract proofs from SAT solver
	Inference* inf = new Inference1(Inference::GLOBAL_SUBSUMPTION, cl);
	Clause* replacement = Clause::fromIterator(LiteralStack::Iterator(survivors),
	    cl->inputType(), inf);
	LOGV(cl->toString());
	LOGV(replacement->toString());
	env.statistics->globalSubsumption++;
	ALWAYS(simplPerformer->willPerform(0));
	simplPerformer->perform(0, replacement);
	ALWAYS(!simplPerformer->clauseKept());

	solver.retractAllAssumptions();
	return;
      }
    }
    solver.retractAllAssumptions();
  }
}

}
