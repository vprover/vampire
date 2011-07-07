/**
 * @file IGAlgorithm.cpp
 * Implements class IGAlgorithm.
 */

#include <cmath>
#include <sstream>

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"
#include "Lib/ScopedLet.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"

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
#include "ModelPrinter.hpp"

#undef LOGGING
#define LOGGING 0

namespace InstGen
{

using namespace Indexing;
using namespace Saturation;

IGAlgorithm::IGAlgorithm()
: _instGenResolutionRatio(env.options->instGenResolutionRatioInstGen(),
    env.options->instGenResolutionRatioResolution(), 50)
{
  CALL("IGAlgorithm::IGAlgorithm");

  _passive.setAgeWeightRatio(env.options->ageRatio(), env.options->weightRatio());

  _satSolver = new TWLSolver(true);

  if(env.options->globalSubsumption()) {
    _groundingIndex = new GroundingIndex(new GlobalSubsumptionGrounder());
    _globalSubsumption = new GlobalSubsumption(_groundingIndex.ptr());
  }

//  if(env.options->unitResultingResolution()) {
//    _unitLitIndex = new UnitClauseLiteralIndex(new LiteralSubstitutionTree());
//    _unitLitIndex->attachContainer(&_resolutionContainer);
//    _nonUnitLitIndex = new NonUnitClauseLiteralIndex(new LiteralSubstitutionTree());
//    _nonUnitLitIndex->attachContainer(&_resolutionContainer);
//    _urResolution = new URResolution(false, _unitLitIndex.ptr(), _nonUnitLitIndex.ptr());
//  }

  if(env.options->instGenWithResolution()) {
    _saturationIndexManager = new IndexManager(0);
    if(env.options->globalSubsumption()) {
      _saturationIndexManager->provideIndex(GLOBAL_SUBSUMPTION_INDEX, _groundingIndex.ptr());
    }
    Options saOptions = *env.options;
    saOptions.setSaturationAlgorithm(Options::OTTER);
    saOptions.setPropositionalToBDD(false);
    saOptions.setSplitting(Options::SM_OFF);
    ScopedLet<Options> slet(*env.options, saOptions);

    _saturationAlgorithm = SaturationAlgorithm::createFromOptions(_saturationIndexManager.ptr());
    _saturationAlgorithm->getSimplifyingClauseContainer()->addedEvent.subscribe(this, &IGAlgorithm::onResolutionClauseDerived);
  }
  else {
    //if there's no resolution, we always do instGen
    _instGenResolutionRatio.alwaysDoFirst();
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

ClauseIterator IGAlgorithm::getActive()
{
  CALL("IGAlgorithm::getActive");

  return pvi( RCClauseStack::Iterator(_active) );
}

void IGAlgorithm::addInputClauses(ClauseIterator it)
{
  CALL("IGAlgorithm::addInputClauses");

  UnitList* units = 0;
  UnitList::pushFromIterator(it, units);

  if(_saturationAlgorithm) {
    ClauseStack copies;
    UnitList::Iterator uit(units);
    while(uit.hasNext()) {
      Clause* cl = static_cast<Clause*>(uit.next());
      Clause* copyCl = Clause::fromIterator(Clause::Iterator(*cl), cl->inputType(), new Inference1(Inference::REORDER_LITERALS, cl));
      copies.push(copyCl);
    }
    _saturationAlgorithm->addInputClauses(pvi( ClauseStack::Iterator(copies) ));
    _saturationAlgorithm->init();
  }

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

    if(unif.clause->length()==1) {
      //we make sure the unit is added first, so that it can be used to shorten the
      //second clause by global subsumption
      tryGeneratingClause(unif.clause, *unif.substitution, false, cl);
      tryGeneratingClause(cl, *unif.substitution, true, unif.clause);
    }
    else {
      tryGeneratingClause(cl, *unif.substitution, true, unif.clause);
      tryGeneratingClause(unif.clause, *unif.substitution, false, cl);
    }
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

void IGAlgorithm::onResolutionClauseDerived(Clause* cl)
{
  CALL("IGAlgorithm::onResolutionClauseDerived");

  if(!cl->noProp() || cl->noSplits()) {
    return;
  }

  SATClauseIterator scit = _gnd.ground(cl);
  scit = Preprocess::removeDuplicateLiterals(scit); //this is required by the SAT solver

  LOG("Solver res clause propagation started");
  _satSolver->ensureVarCnt(_gnd.satVarCnt());
  _satSolver->addClauses(scit, true);
  LOG("Solver res clause propagation finished");

  if(_satSolver->getStatus()==SATSolver::UNSATISFIABLE) {
    Clause* foRefutation = getFORefutation(_satSolver->getRefutation());
    throw RefutationFoundException(foRefutation);
  }
}

void IGAlgorithm::doResolutionStep()
{
  CALL("IGAlgorithm::doResolutionStep");

  if(!_saturationAlgorithm) {
    return;
  }

  try {
    _saturationAlgorithm->doOneAlgorithmStep();
  }
  catch(MainLoopFinishedException e)
  {
    switch(e.result.terminationReason) {
    case Statistics::REFUTATION:
    case Statistics::SATISFIABLE:
      throw;
    case Statistics::REFUTATION_NOT_FOUND:
    case Statistics::UNKNOWN:
    case Statistics::TIME_LIMIT:
    case Statistics::MEMORY_LIMIT:
      //refutation algorithm finished, we just get rid of it
      _saturationAlgorithm = SaturationAlgorithmSP();
      _instGenResolutionRatio.alwaysDoFirst();
      break;
    }
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

  RCClauseStack::Iterator icit(_inputClauses);
  while(icit.hasNext()) {
    Clause* cl = icit.next();
    if(isRefutation(cl)) {
      throw RefutationFoundException(cl);
    }
    addClause(cl);
  }

  int restartRatioMultiplier = 100;
  int bigRestartRatio = static_cast<int>(restartRatioMultiplier * env.options->instGenBigRestartRatio());
  int smallRestartRatio = restartRatioMultiplier - bigRestartRatio;

  int restartKindRatio = 0;

  unsigned loopIterBeforeRestart = env.options->instGenRestartPeriod();

  for(;;) {
    bool restarting = false;
    unsigned loopIterCnt = 0;
    while(_unprocessed.isNonEmpty() || !_passive.isEmpty()) {
      env.statistics->instGenIterations++;
      processUnprocessed();
      ASS_EQ(_satSolver->getStatus(), SATSolver::SATISFIABLE);

      unsigned activatedCnt = max(10u, _passive.size()/4);
      for(unsigned i=0; i<activatedCnt && !_passive.isEmpty() && _instGenResolutionRatio.shouldDoFirst(); i++) {
	Clause* given = _passive.popSelected();
	activate(given);
	_instGenResolutionRatio.doFirst();
	if(loopIterBeforeRestart && ++loopIterCnt > loopIterBeforeRestart) {
	  restarting = true;
	  break;
	}
      }

      doReactivation();

      if(restarting) {
	break;
      }

      while(_instGenResolutionRatio.shouldDoSecond()) {
	doResolutionStep();
	_instGenResolutionRatio.doSecond();
      }
      env.checkTimeSometime<100>();
    }
    if(restarting) {
      if(restartKindRatio>0) {
	restartFromBeginning();
	restartKindRatio -= smallRestartRatio;
      }
      else {
	//if we ran out of clauses, we need this kind of restart to check for satisfiability
	restartWithCurrentClauses();
	restartKindRatio += bigRestartRatio;
      }
      loopIterBeforeRestart = static_cast<int>(ceilf(
	  loopIterBeforeRestart*env.options->instGenRestartPeriodQuotient()));

    }
    else {
      //we're here because there were no more clauses to activate
      restartWithCurrentClauses();
    }
    processUnprocessed();
    while(!_passive.isEmpty()) {
      Clause* given = _passive.popSelected();
      activate(given);
    }
    if(_unprocessed.isEmpty()) {
      if(env.options->complete()) {
	if(env.options->proof()!=Options::PROOF_OFF) {
	  stringstream modelStm;
	  ModelPrinter(*this).tryOutput(modelStm);
	  env.statistics->model = modelStm.str();
	}
	return MainLoopResult(Statistics::SATISFIABLE);
      }
      else {
	return MainLoopResult(Statistics::REFUTATION_NOT_FOUND);
      }
    }
  }
}

}
