/**
 * @file IGAlgorithm.cpp
 * Implements class IGAlgorithm.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

#include "Indexing/LiteralSubstitutionTree.hpp"

#include "SAT/Preprocess.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/TWLSolver.hpp"

#include "IGAlgorithm.hpp"

#undef LOGGING
#define LOGGING 1
//TODO:Equality
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
    addClause(it.next());
  }
}

void IGAlgorithm::addClause(Clause* cl)
{
  CALL("IGAlgorithm::addClause");

  cl = _dlr.simplify(cl);
  if(_variantIdx.retrieveVariants(cl).hasNext()) {
    return;
  }
  _variantIdx.insert(cl);

  _unprocessed.push(cl);
}

void IGAlgorithm::processUnprocessed()
{
  CALL("IGAlgorithm::processUnprocessed");

  static SATClauseStack satClauses;
  satClauses.reset();

  while(_unprocessed.isNonEmpty()) {
    Clause* cl = _unprocessed.pop();

    _active.push(cl);

//    LOG("Added clause "<<cl->toString());
    SATClause* sc = _gnd.ground(cl);
    satClauses.push(sc);
  }
  _satSolver->ensureVarCnt(_gnd.satVarCnt());

  SATClauseIterator scit = pvi( SATClauseStack::Iterator(satClauses) );
  scit = Preprocess::removeDuplicateLiterals(scit); //this is required by the SAT solver

  LOG("Solver started");
  _satSolver->addClauses(scit);
  LOG("Solver finished");
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

  ClauseStack::Iterator cit(_active);
  while(cit.hasNext()) {
    Clause* cl = cit.next();
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

  ClauseStack::Iterator cit(_active);
  while(cit.hasNext()) {
    Clause* cl = cit.next();
    unsigned clen = cl->length();
    for(unsigned i=0; i<clen; i++) {
      if(!isSelected((*cl)[i])) {
	continue;
      }
      tryGeneratingInstances(cl, i, selected);
    }
    if(_unprocessed.size()>_active.size()) {
      return;
    }
  }
}

IGAlgorithm::TerminationReason IGAlgorithm::run()
{
  CALL("IGAlgorithm::process");
  LOG("IGA started");

  while(_unprocessed.isNonEmpty()) {
    processUnprocessed();

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
