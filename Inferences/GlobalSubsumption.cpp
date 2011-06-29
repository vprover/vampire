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
#include "Kernel/InferenceStore.hpp"

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
 * Add clause to the SATSolver in the index. If the resuting set is
 * unsatisfiable, it means we have a refutation and
 * @c MainLoop::RefutationFoundException is thrown.
 */
void GlobalSubsumption::addClauseToIndex(Clause* cl)
{
  CALL("GlobalSubsumption::addClauseToIndex");

  SATSolver& solver = _index->getSolver();
  Grounder& grounder = _index->getGrounder();

  ASS_EQ(solver.getStatus(),SATSolver::SATISFIABLE);

  SATClauseIterator sclIt = grounder.ground(cl);
  solver.ensureVarCnt(grounder.satVarCnt());
  solver.addClauses(sclIt, true);

  if(solver.getStatus()==SATSolver::UNSATISFIABLE) {
    //just a dummy inference, the correct one will be in the InferenceStore
    Inference* inf = new Inference(Inference::TAUTOLOGY_INTRODUCTION);
    Clause* refutation = Clause::fromIterator(LiteralIterator::getEmpty(), Unit::CONJECTURE, inf);
    refutation->setAge(cl->age());

    recordInference(cl, solver.getRefutation(), refutation);

    env.statistics->globalSubsumption++;
    throw MainLoop::RefutationFoundException(refutation);
  }
  ASS_EQ(solver.getStatus(),SATSolver::SATISFIABLE);
}

void GlobalSubsumption::recordInference(Clause* origClause, SATClause* refutation, Clause* resultClause)
{
  CALL("GlobalSubsumption::recordInference");
  ASS(refutation);

  typedef InferenceStore::UnitSpec UnitSpec;

  static Stack<UnitSpec> prems;
  static Stack<SATClause*> toDo;
  static DHSet<SATClause*> seen;
  prems.reset();
  toDo.reset();
  seen.reset();

  prems.push(UnitSpec(origClause));

  toDo.push(refutation);
  while(toDo.isNonEmpty()) {
    SATClause* cur = toDo.pop();
    if(!seen.insert(cur)) {
      continue;
    }
    SATInference* sinf = cur->inference();
    ASS(sinf);
    switch(sinf->getType()) {
    case SATInference::FO_CONVERSION:
      prems.push(static_cast<FOConversionInference*>(sinf)->getOrigin());
      break;
    case SATInference::ASSUMPTION:
      break;
    case SATInference::PROP_INF:
    {
      PropInference* pinf = static_cast<PropInference*>(sinf);
      toDo.loadFromIterator(SATClauseList::Iterator(pinf->getPremises()));
      break;
    }
    default:
      ASSERTION_VIOLATION;
    }
  }

  makeUnique(prems);
  unsigned premCnt = prems.size();

  InferenceStore::FullInference* inf = new(premCnt) InferenceStore::FullInference(premCnt);
  inf->rule = Inference::GLOBAL_SUBSUMPTION;

  for(unsigned i=0; i<premCnt; i++) {
    LOGV(prems[i].toString());
    inf->premises[i] = prems[i];
  }

  InferenceStore::instance()->recordInference(UnitSpec(resultClause), inf);
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

  addClauseToIndex(cl);

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

	//just a dummy inference, the correct one will be in the InferenceStore
	Inference* inf = new Inference(Inference::TAUTOLOGY_INTRODUCTION);
	Clause* replacement = Clause::fromIterator(LiteralStack::Iterator(survivors),
	    cl->inputType(), inf);
	replacement->setAge(cl->age());

	recordInference(cl, solver.getRefutation(), replacement);
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
