/**
 * @file IGAlgorithm.cpp
 * Implements class IGAlgorithm.
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

#include "Indexing/LiteralSubstitutionTree.hpp"

#include "SAT/Preprocess.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/TWLSolver.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/EqualityProxy.hpp"
#include "Shell/Options.hpp"
#include "Shell/Property.hpp"
#include "Shell/Statistics.hpp"

#include "IGAlgorithm.hpp"

#undef LOGGING
#define LOGGING 0

namespace InstGen
{

using namespace Indexing;

IGAlgorithm::IGAlgorithm()
{
  CALL("IGAlgorithm::IGAlgorithm");

  _satSolver = new TWLSolver(true);

  if(env.options->globalSubsumption()) {
    _groundingIndex = new GroundingIndex(new GlobalSubsumptionGrounder());
    _globalSubsumption = new GlobalSubsumption(_groundingIndex.ptr());
  }
}

IGAlgorithm::~IGAlgorithm()
{
  CALL("IGAlgorithm::~IGAlgorithm");
}

void IGAlgorithm::addInputClauses(ClauseIterator it)
{
  CALL("IGAlgorithm::addInputClauses");

  UnitList* units = 0;
  UnitList::pushFromIterator(it, units);

  Property property;
  property.scan(units);
  if(property.equalityAtoms()) {
    EqualityProxy ep(Options::EP_RSTC);
    ep.apply(units);
  }

  while(units) {
    Clause* cl = static_cast<Clause*>(UnitList::pop(units));
    ASS(cl->isClause());
    addClause(cl);
  }
}

void IGAlgorithm::addClause(Clause* cl)
{
  CALL("IGAlgorithm::addClause");

  cl = _duplicateLiteralRemoval.simplify(cl);
  cl = _tautologyDeletion.simplify(cl);
  if(!cl) {
    return;
  }
//  cout<<endl<<endl<<"---------"<<endl;
//  cout<<"init: "<<cl->toString()<<endl;

redundancy_check:
  if(_variantIdx.retrieveVariants(cl).hasNext()) {
    cl->destroyIfUnnecessary();
    env.statistics->instGenRedundantClauses++;
//    cout<<endl<<endl<<"## is variant ##"<<endl;
    return;
  }
  cl->incRefCnt();
  _variantIdx.insert(cl);
  if(_globalSubsumption) {
    Clause* newCl = _globalSubsumption->perform(cl);
    if(newCl!=cl) {
      ASS_L(newCl->length(), cl->length());
      ASS_G(newCl->length(), 0);

//      cout<<"gs:   "<<newCl->toString()<<endl;

      cl = newCl;
      goto redundancy_check;
    }
  }
//  cout<<endl<<endl<<"## survived ##"<<endl;

  _unprocessed.push(cl);
  env.statistics->instGenKeptClauses++;
}

void IGAlgorithm::processUnprocessed()
{
  CALL("IGAlgorithm::processUnprocessed");

  static SATClauseStack satClauses;
  satClauses.reset();

  while(_unprocessed.isNonEmpty()) {
    Clause* cl = _unprocessed.popWithoutDec();

    _active.push(cl);
    cl->decRefCnt(); //corresponds to _unprocessed.popWithoutDec();

    SATClauseIterator sc = _gnd.ground(cl);
    satClauses.loadFromIterator(sc);
  }
  _satSolver->ensureVarCnt(_gnd.satVarCnt());

  SATClauseIterator scit = pvi( SATClauseStack::Iterator(satClauses) );
  scit = Preprocess::removeDuplicateLiterals(scit); //this is required by the SAT solver

  LOG("Solver started");
  _satSolver->addClauses(scit);
  LOG("Solver finished");

  if(_satSolver->getStatus()==SATSolver::UNSATISFIABLE) {
    Clause* foRefutation = getFORefutation(_satSolver->getRefutation());
    throw RefutationFoundException(foRefutation);
  }
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

  RCClauseStack::Iterator cit(_active);
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
void IGAlgorithm::tryGeneratingClause(Clause* orig, ResultSubstitution& subst, bool isQuery)
{
  CALL("IGAlgorithm::tryGeneratingClause");

  static LiteralStack genLits;
  genLits.reset();

  bool properInstance = false;
  unsigned clen = orig->length();
  for(unsigned i=0; i<clen; i++) {
    Literal* olit = (*orig)[i];
    Literal* glit = isQuery ? subst.applyToQuery(olit) : subst.applyToResult(olit);
    genLits.push(glit);
    if(olit!=glit) {
      properInstance = true;
    }
  }
  if(!properInstance) {
    return;
  }
  Inference* inf = new Inference1(Inference::INSTANCE_GENERATION, orig);
  Clause* res = Clause::fromStack(genLits, orig->inputType(), inf);
  res->setAge(orig->age()+1);

  env.statistics->instGenGeneratedClauses++;
  addClause(res);
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

    tryGeneratingClause(cl, *unif.substitution, true);
    tryGeneratingClause(unif.clause, *unif.substitution, false);
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

  RCClauseStack::Iterator cit(_active);
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

Clause* IGAlgorithm::getFORefutation(SATClause* satRefutation)
{
  CALL("IGAlgorithm::getFORefutation");
  ASS(satRefutation);

  //just a dummy inference, the correct one will be in the inference store
  Inference* inf = new Inference(Inference::TAUTOLOGY_INTRODUCTION);
  Clause* res = Clause::fromIterator(LiteralIterator::getEmpty(), Unit::CONJECTURE, inf);
  Grounder::recordInference(0, satRefutation, res);
  return res;
}

MainLoopResult IGAlgorithm::runImpl()
{
  CALL("IGAlgorithm::runImpl");
  LOG("IGA started");

  while(_unprocessed.isNonEmpty() || !_passive.isEmpty()) {
    env.statistics->instGenIterations++;
    processUnprocessed();

    ASS_EQ(_satSolver->getStatus(), SATSolver::SATISFIABLE);
    generateInstances();
    LOG("IGA loop finished");
  }

  return MainLoopResult(Statistics::SATISFIABLE);
}

}
