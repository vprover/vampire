/**
 * @file IGAlgorithm.cpp
 * Implements class IGAlgorithm.
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"
#include "Lib/TimeCounter.hpp"

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

  _passive.setAgeWeightRatio(env.options->ageRatio(), env.options->weightRatio());

  _satSolver = new TWLSolver(true);

  if(env.options->globalSubsumption()) {
    _groundingIndex = new GroundingIndex(new GlobalSubsumptionGrounder());
    _globalSubsumption = new GlobalSubsumption(_groundingIndex.ptr());
  }

  _variantIdx = new ClauseVariantIndex();
  _selected = new LiteralSubstitutionTree();
}

IGAlgorithm::~IGAlgorithm()
{
  CALL("IGAlgorithm::~IGAlgorithm");

  delete _selected;
  delete _variantIdx;
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
    _inputClauses.push(cl);
    addClause(cl);
  }
}

void IGAlgorithm::addClause(Clause* cl)
{
  CALL("IGAlgorithm::addClause");

  TimeCounter tc(TC_INST_GEN_SIMPLIFICATIONS);

  cl = _duplicateLiteralRemoval.simplify(cl);
  cl = _tautologyDeletion.simplify(cl);
  if(!cl) {
    return;
  }
//  cout<<endl<<endl<<"---------"<<endl;
//  cout<<"init: "<<cl->toString()<<endl;

redundancy_check:
  if(_variantIdx->retrieveVariants(cl).hasNext()) {
    cl->destroyIfUnnecessary();
    env.statistics->instGenRedundantClauses++;
//    cout<<endl<<endl<<"## is variant ##"<<endl;
    return;
  }
  cl->incRefCnt();
  _variantIdx->insert(cl);
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

void IGAlgorithm::processUnprocessed()
{
  CALL("IGAlgorithm::processUnprocessed");

  TimeCounter tc(TC_INST_GEN_SAT_SOLVING);

  static SATClauseStack satClauses;
  satClauses.reset();

  while(_unprocessed.isNonEmpty()) {
    Clause* cl = _unprocessed.popWithoutDec();

    //we should do cl->decRefCnt() here, but passive doesn't increase on its own,
    //so it cancels out with the increase we'd have to do for it
    _passive.add(cl);

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
 * Generate an instance clause from @c orig using substitution @c subst. Either
 * query or result part of the substitution @c subst is used, based on the
 * value of @c isQuery.
 */
void IGAlgorithm::tryGeneratingClause(Clause* orig, ResultSubstitution& subst, bool isQuery, Clause* otherCl)
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
  int newAge = max(orig->age(), otherCl->age())+1;
  res->setAge(newAge);

  env.statistics->instGenGeneratedClauses++;
  addClause(res);
}

/**
 * Generate instances from literal of index @c litIdx in clause @c cl,
 * using the selected literals in @c selected index.
 */
void IGAlgorithm::tryGeneratingInstances(Clause* cl, unsigned litIdx)
{
  CALL("IGAlgorithm::tryGeneratingInstances");

  Literal* lit = (*cl)[litIdx];

  SLQueryResultIterator unifs = _selected->getUnifications(lit, true, true);
  while(unifs.hasNext()) {
    SLQueryResult unif = unifs.next();
    if(!isSelected(unif.literal)) {
      deactivate(unif.clause);
      continue;//literal is no longer selected
    }

    tryGeneratingClause(cl, *unif.substitution, true, unif.clause);
    tryGeneratingClause(unif.clause, *unif.substitution, false, cl);
  }
}

///**
// * Insert selected literals into the @c acc index.
// */
//void IGAlgorithm::collectSelected(LiteralSubstitutionTree& acc)
//{
//  CALL("IGAlgorithm::collectSelected");
//
//  RCClauseStack::Iterator cit(_active);
//  while(cit.hasNext()) {
//    Clause* cl = cit.next();
//    unsigned clen = cl->length();
//    for(unsigned i=0; i<clen; i++) {
//      if(!isSelected((*cl)[i])) {
//	continue;
//      }
//      acc.insert((*cl)[i], cl);
//    }
//  }
//}


/**
 * Insert selected literals of @c cl into the @c _selected index.
 */
void IGAlgorithm::selectAndAddToIndex(Clause* cl)
{
  CALL("IGAlgorithm::selectAndAddToIndex");

  bool modified = false;
  unsigned selIdx = 0;

  unsigned clen = cl->length();
  for(unsigned i=0; i<clen; i++) {
    if(!isSelected((*cl)[i])) {
      continue;
    }

    LOG("selected: "<<(*cl)[i]->toString());
    _selected->insert((*cl)[i], cl);

    if(selIdx!=i) {
      modified = true;
      swap((*cl)[i], (*cl)[selIdx]);
    }
    selIdx++;
  }
  ASS_REP(selIdx>0, cl->toString());
  if(modified) {
    cl->notifyLiteralReorder();
  }
  cl->setSelected(selIdx);
}

void IGAlgorithm::removeFromIndex(Clause* cl)
{
  CALL("IGAlgorithm::removeFromIndex");

  unsigned selCnt = cl->selected();
  for(unsigned i=0; i<selCnt; i++) {
    _selected->remove((*cl)[i], cl);
  }
}

void IGAlgorithm::activate(Clause* cl, bool wasDeactivated)
{
  CALL("IGAlgorithm::activate");

  LOG("activating "<<cl->toString());
  selectAndAddToIndex(cl);

  unsigned clen = cl->length();
  for(unsigned i=0; i<clen; i++) {
    if(!isSelected((*cl)[i])) {
	continue;
    }
    tryGeneratingInstances(cl, i);
  }

  if(!wasDeactivated) {
    _active.push(cl);
    cl->decRefCnt(); //this decrease corresponds to the removal from the passive container
  }
}

void IGAlgorithm::deactivate(Clause* cl)
{
  CALL("IGAlgorithm::deactivate");

  if(_deactivatedSet.insert(cl)) {
//    cout<<"Deactivated: "<<cl->toString()<<endl;
    _deactivated.push(cl);
  }
}

void IGAlgorithm::doReactivation()
{
  CALL("IGAlgorithm::doReactivation");

  static ClauseStack toActivate;
  toActivate.reset();

  ClauseStack::Iterator dit(_deactivated);
  while(dit.hasNext()) {
    Clause* cl = dit.next();
//    cout<<"Reactivating: "<<cl->toString()<<endl;
    removeFromIndex(cl);
    selectAndAddToIndex(cl);
    toActivate.push(cl);
  }

  _deactivated.reset();
  _deactivatedSet.reset();
  while(toActivate.isNonEmpty()) {
    Clause* cl = toActivate.pop();
    activate(cl, true);
  }
}

void IGAlgorithm::wipeIndexes()
{
  CALL("IGAlgorithm::wipeIndexes");

  _deactivated.reset();
  _deactivatedSet.reset();

  delete _selected;
  delete _variantIdx;
  _variantIdx = new ClauseVariantIndex();
  _selected = new LiteralSubstitutionTree();
}

void IGAlgorithm::restartWithCurrentClauses()
{
  CALL("IGAlgorithm::restartWithCurrentClauses");

  LOG("restartWithCurrentClauses");

  static ClauseStack allClauses;
  allClauses.reset();

  while(_active.isNonEmpty()) {
    allClauses.push(_active.popWithoutDec());
  }
  while(!_passive.isEmpty()) {
    allClauses.push(_passive.popSelected());
  }
  while(_unprocessed.isNonEmpty()) {
    allClauses.push(_unprocessed.popWithoutDec());
  }

  wipeIndexes();

  while(allClauses.isNonEmpty()) {
    Clause* cl = allClauses.pop();
    addClause(cl);
    cl->decRefCnt();//corresponds to the removal from the active and passive container
  }
}

void IGAlgorithm::restartFromBeginning()
{
  CALL("IGAlgorithm::restartFromBeginning");

  _active.reset();
  while(!_passive.isEmpty()) {
    Clause* cl = _passive.popSelected();
    cl->decRefCnt();
  }
  _unprocessed.reset();

  wipeIndexes();

  RCClauseStack::Iterator icit(_inputClauses);
  while(icit.hasNext()) {
    Clause* cl = icit.next();
    addClause(cl);
  }
}


MainLoopResult IGAlgorithm::runImpl()
{
  CALL("IGAlgorithm::runImpl");
  LOG("IGA started");

  unsigned loopIterBeforeRestart = 50;

  for(;;) {
    unsigned loopIterCnt = 0;
    while(_unprocessed.isNonEmpty() || !_passive.isEmpty()) {
      env.statistics->instGenIterations++;
      processUnprocessed();
      ASS_EQ(_satSolver->getStatus(), SATSolver::SATISFIABLE);

      unsigned activatedCnt = max(10u, _passive.size()/4);
      for(unsigned i=0; i<activatedCnt && !_passive.isEmpty(); i++) {
	Clause* given = _passive.popSelected();
	activate(given);
      }

      doReactivation();

      if(++loopIterCnt == loopIterBeforeRestart) {
	break;
      }

      env.checkTimeSometime<100>();
    }
//    if(loopIterCnt == loopIterBeforeRestart && Random::getInteger()%2==0) {
//      restartFromBeginning();
//      loopIterBeforeRestart *= 2;
//    }
//    else {
      //if we ran out of clauses, we need this kind of restart to check for satisfiability
      restartWithCurrentClauses();
//    }
    processUnprocessed();
    while(!_passive.isEmpty()) {
      Clause* given = _passive.popSelected();
      activate(given);
    }
    if(_unprocessed.isEmpty()) {
      return MainLoopResult(Statistics::SATISFIABLE);
    }
  }
}

}
