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
#include "SAT/SATInference.hpp"

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
 * Add clause to the SATSolver in the index.
 * The clause has already been grounded and the corresponding literals come in @b satLits,
 * but a propositional clause now needs to be created from them.
 *
 * If the resulting set is
 * unsatisfiable, it means we have a refutation and
 * @c MainLoop::RefutationFoundException is thrown.
 */
void GlobalSubsumption::addClauseToIndex(Clause* cl, SATLiteralStack& satLits)
{
  CALL("GlobalSubsumption::addClauseToIndex");

  SATSolver& solver = _index->getSolver();
  Grounder& grounder = _index->getGrounder();

  ASS_NEQ(solver.solve(_uprOnly),SATSolver::UNSATISFIABLE);

  SATClause* scl = SATClause::fromStack(satLits);
  SATInference* inf = new FOConversionInference(UnitSpec(cl));
  scl->setInference(inf);

  solver.ensureVarCount(grounder.satVarCnt());
  solver.addClause(scl);

  if(solver.solve(_uprOnly)==SATSolver::UNSATISFIABLE) {
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

  Grounder& grounder = _index->getGrounder();
  SATSolverWithAssumptions& solver = _index->getSolver();

  static SATLiteralStack slits;
  slits.reset();
  grounder.groundNonProp(cl, slits, false);

  addClauseToIndex(cl,slits);

  if(cl->length()==1) {
    return cl;
  }

  unsigned clen = slits.size();

  static DHMap<SATLiteral,Literal*> lookup;
  lookup.reset();
  static SATLiteralStack assumps;
  assumps.reset();
  for (unsigned i = 0; i < clen; i++) {
    lookup.insert(slits[i],(*cl)[i]);
    assumps.push(slits[i].opposite());
  }

  SATSolver::Status res = solver.solveUnderAssumptions(assumps, _uprOnly, true /* only proper subsets */);

  if (res == SATSolver::UNSATISFIABLE) {
    const SATLiteralStack& failed = solver.failedAssumptions();

    if (failed.size() < assumps.size()) {
      static LiteralStack survivors;
      survivors.reset();

      for (unsigned i = 0; i < failed.size(); i++) {
        survivors.push(lookup.get(failed[i].opposite())); // back to the original polarity to lookup the corresponding FO literal
      }

      //just a dummy inference, the correct one will be in the InferenceStore
      Inference* inf = new Inference(Inference::TAUTOLOGY_INTRODUCTION);
      Clause* replacement = Clause::fromIterator(LiteralStack::BottomFirstIterator(survivors),cl->inputType(), inf);
      replacement->setAge(cl->age());

      Grounder::recordInference(cl, solver.getRefutation(), replacement);
      env.statistics->globalSubsumption++;
      ASS_L(replacement->length(), clen);

      return replacement;
    }
  }

  return cl;
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
