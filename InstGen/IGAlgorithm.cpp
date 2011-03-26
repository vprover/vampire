/**
 * @file IGAlgorithm.cpp
 * Implements class IGAlgorithm.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

#include "Indexing/LiteralSubstitutionTree.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/TWLSolver.hpp"

#include "IGAlgorithm.hpp"

#undef LOGGING
#define LOGGING 0

namespace InstGen
{

using namespace Indexing;

IGAlgorithm::IGAlgorithm()
{
  CALL("IGAlgorithm::IGAlgorithm");

  _satSolver = new TWLSolver();
}

/**
 * Add clauses from @c it among unprocessed
 */
void IGAlgorithm::addClauses(ClauseIterator it)
{
  CALL("IGAlgorithm::addClauses");

  while(it.hasNext()) {
    Clause* cl = it.next();
    if(_variantIdx.retrieveVariants(cl).hasNext()) {
      continue;
    }
    LOG("Generated "<<cl->toString());
    SATClause* sc = _gnd.ground(cl);
    _s2c.insert(sc, cl);
    _c2s.insert(cl, sc);
    _unprocessed.push(sc);
    _variantIdx.insert(cl);
  }
  _satSolver->ensureVarCnt(_gnd.satVarCnt());
}

void IGAlgorithm::addClause(Clause* cl)
{
  CALL("IGAlgorithm::addClause");

  addClauses( pvi(getSingletonIterator(cl)) );
}

bool IGAlgorithm::isSelected(Literal* lit)
{
  CALL("IGAlgorithm::isSelected");

  return _satSolver->trueInAssignment(_gnd.ground(lit));
}

/**
 * Insert selected literals into the @c acc index.
 */
void IGAlgorithm::collectSelected(LiteralSubstitutionTree& acc)
{
  CALL("IGAlgorithm::collectSelected");

  SATClauseStack::Iterator scit(_active);
  while(scit.hasNext()) {
    SATClause* sc = scit.next();
    Clause* cl = _s2c.get(sc);
    ASS_EQ(sc->length(), cl->length()); //corresponding clauses must have the same length
    unsigned clen = cl->length();
    for(unsigned i=0; i<clen; i++) {
      if(!isSelected((*cl)[i])) {
	continue;
      }
      acc.insert((*cl)[i], cl);
    }
  }
}

/**
 * Generate an instance clause from @c orig using substitution @c subst. Either
 * query or result part of the substitution @c subst is used, based on the
 * value of @c isQuery.
 */
Clause* IGAlgorithm::generateClause(Clause* orig, ResultSubstitution& subst, bool isQuery)
{
  CALL("IGAlgorithm::generateClause");

  static LiteralStack genLits;
  genLits.reset();

  unsigned clen = orig->length();
  for(unsigned i=0; i<clen; i++) {
    Literal* olit = (*orig)[i];
    Literal* glit = isQuery ? subst.applyToQuery(olit) : subst.applyToResult(olit);
    genLits.push(glit);
  }
  Inference* inf = new Inference1(Inference::INSTANCE_GENERATION, orig);
  Clause* res = Clause::fromStack(genLits, orig->inputType(), inf);
  return res;
}

/**
 * Generate instances from literal of index @c litIdx in clause @c cl,
 * using the selected literals in @c selected index.
 */
void IGAlgorithm::tryGeneratingInstances(Clause* cl, unsigned litIdx, LiteralSubstitutionTree& selected)
{
  CALL("IGAlgorithm::tryGeneratingInstances");

  Literal* lit = (*cl)[litIdx];

  SLQueryResultIterator unifs = selected.getUnifications(lit, true, true);
  while(unifs.hasNext()) {
    SLQueryResult unif = unifs.next();

    addClause(generateClause(cl, *unif.substitution, true));
    addClause(generateClause(unif.clause, *unif.substitution, false));
  }
}

/**
 * Generate instances based on the assignment in the SAT solver,
 * and add these instanced among unprocessed clauses.
 */
void IGAlgorithm::generateInstances()
{
  CALL("IGAlgorithm::generateInstances");
  ASS_EQ(_satSolver->getStatus(), SATSolver::SATISFIABLE);

  LiteralSubstitutionTree selected;

  collectSelected(selected);

  SATClauseStack::Iterator scit(_active);
  while(scit.hasNext()) {
    SATClause* sc = scit.next();
    Clause* cl = _s2c.get(sc);
    unsigned clen = cl->length();
    for(unsigned i=0; i<clen; i++) {
      if(!isSelected((*cl)[i])) {
	continue;
      }
      tryGeneratingInstances(cl, i, selected);
    }
  }
}

IGAlgorithm::TerminationReason IGAlgorithm::process()
{
  CALL("IGAlgorithm::process");
  LOG("IGA started");

  while(_unprocessed.isNonEmpty()) {
    LOG("Solver started");
    _satSolver->addClauses(pvi( SATClauseStack::Iterator(_unprocessed) ));
    LOG("Solver finished");
    _active.loadFromIterator(SATClauseStack::Iterator(_unprocessed));
    _unprocessed.reset();

    if(_satSolver->getStatus()==SATSolver::UNSATISFIABLE) {
      return Statistics::REFUTATION;
    }
    ASS_EQ(_satSolver->getStatus(), SATSolver::SATISFIABLE);
    generateInstances();
    LOG("IGA loop finished");
  }

  return Statistics::SATISFIABLE;
}

}
