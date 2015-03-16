/**
 * @file GlobalSubsumption.cpp
 * Implements class GlobalSubsumption.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/VirtualIterator.hpp"

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

  if(_allowExtraAttachment) {
    return;
  }
  ASS(!_index);

  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<GroundingIndex*>(
	  _salg->getIndexManager()->request(GLOBAL_SUBSUMPTION_INDEX) );
}

void GlobalSubsumption::detach()
{
  CALL("GlobalSubsumption::detach");

  if(_allowExtraAttachment) {
    return;
  }

  _index=0;
  _salg->getIndexManager()->release(GLOBAL_SUBSUMPTION_INDEX);
  ForwardSimplificationEngine::detach();
}

/**
 * Add clause to the SATSolver in the index. If the resuting set is
 * unsatisfiable, it means we have a refutation and
 * @c MainLoop::RefutationFoundException is thrown.
 */
void GlobalSubsumption::addClauseToIndex(Clause* cl)
{
  CALL("GlobalSubsumption::addClauseToIndex");

  SATSolver& solver = _index->getSolver();
  Grounder& grounder = _index->getGrounder();

  // ASS_NEQ(solver.getStatus(),SATSolver::UNSATISFIABLE);

  SATClauseIterator sclIt = grounder.ground(cl,false);
  solver.ensureVarCnt(grounder.satVarCnt());
  solver.addClauses(sclIt);

  if(solver.solve(true)==SATSolver::UNSATISFIABLE) {
    //just a dummy inference, the correct one will be in the InferenceStore
    Inference* inf = new Inference(Inference::TAUTOLOGY_INTRODUCTION);
    Clause* refutation = Clause::fromIterator(LiteralIterator::getEmpty(), Unit::CONJECTURE, inf);
    refutation->setAge(cl->age());

    Grounder::recordInference(cl, solver.getRefutation(), refutation);

    env.statistics->globalSubsumption++;
    throw MainLoop::RefutationFoundException(refutation);
  }
}

Clause* GlobalSubsumption::perform(Clause* cl)
{
  CALL("GlobalSubsumption::perform/1");

  TimeCounter tc(TC_GLOBAL_SUBSUMPTION);

  if(cl->splits() && cl->splits()->size()!=0) {
    //Since we don't remove clauses, we must ignore clauses with splitting
    //history, because it wouldn't be possible to backtrack them
    return cl;
  }


  if(cl->color()==COLOR_LEFT) {
    return cl;
  }

  if(cl->length()==1) {
    addClauseToIndex(cl);
    return cl;
  }

  Grounder& grounder = _index->getGrounder();

  static SATLiteralStack slits;
  slits.reset();

  grounder.groundNonProp(cl, slits, false);

  addClauseToIndex(cl);

  unsigned clen = slits.size();


  for(unsigned resolvedIdx = 0; resolvedIdx<clen; resolvedIdx++) {
    Clause* replacement = tryResolvingAway(cl, resolvedIdx, slits);
    if(replacement!=0) {
      return replacement;
    }
  }
  return cl;
}

Clause* GlobalSubsumption::tryResolvingAway(Clause* cl, unsigned litIdx, SATLiteralStack& slits)
{
  CALL("GlobalSubsumption::tryResolvingAway");

  bool uprOnly = true;

  unsigned clen = cl->length();
  SATSolverWithAssumptions& solver = _index->getSolver();

  // for each literal except litIdx (resolved)
  for(unsigned i = 0; i<clen; i++) {
    if(i==litIdx) {
	continue;
    }
    solver.addAssumption(slits[i].opposite());

    if(solver.solve(uprOnly)==SATSolver::UNSATISFIABLE) {
	static LiteralStack survivors;
	survivors.reset();

	for(unsigned j=0; j<=i; j++) {
	  if(j==litIdx) {
	    continue;
	  }
	  survivors.push((*cl)[j]);
	}
//	cout<<cl->length()<<" --> "<<survivors.length()<<"  mi: "<<maskedIdx<<endl;

	//just a dummy inference, the correct one will be in the InferenceStore
	Inference* inf = new Inference(Inference::TAUTOLOGY_INTRODUCTION);
	Clause* replacement = Clause::fromIterator(LiteralStack::BottomFirstIterator(survivors),
	    cl->inputType(), inf);
	replacement->setAge(cl->age());

	Grounder::recordInference(cl, solver.getRefutation(), replacement);
	env.statistics->globalSubsumption++;
        ASS_L(replacement->length(), clen);

	solver.retractAllAssumptions();
	return replacement;
    }
  }
  solver.retractAllAssumptions();
  return 0;
}

void GlobalSubsumption::perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer)
{
  CALL("GlobalSubsumption::perform/2");

  Clause* newCl = perform(cl);
  if(newCl==cl) {
    return;
  }

  ALWAYS(simplPerformer->willPerform(0));
  simplPerformer->perform(0, newCl);
  ALWAYS(!simplPerformer->clauseKept());
}

}
