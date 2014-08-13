/**
 * @file IGAlgorithm.cpp
 * Implements class IGAlgorithm.
 */

#include <cmath>
#include <sstream>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"
#include "Lib/ScopedLet.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/RCClauseStack.hpp"
#include "Kernel/SortHelper.hpp"

#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/LiteralIndex.hpp"

#include "SAT/Preprocess.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/TWLSolver.hpp"
#include "SAT/LingelingInterfacing.hpp"
#include "SAT/BufferedSolver.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/EquivalenceDiscoverer.hpp"
#include "Shell/EqualityAxiomatizer.hpp"
#include "Shell/EqualityProxy.hpp"
#include "Shell/PDInliner.hpp"
#include "Shell/Property.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "IGAlgorithm.hpp"
#include "ModelPrinter.hpp"

#undef LOGGING
#define LOGGING 0

namespace InstGen
{

using namespace Indexing;
using namespace Saturation;

IGAlgorithm::IGAlgorithm(Problem& prb, const Options& opt)
: MainLoop(prb, opt),
    _instGenResolutionRatio(opt.instGenResolutionRatioInstGen(),
	opt.instGenResolutionRatioResolution(), 50),
    _passive(opt),
    _tautologyDeletion(false)
{
  CALL("IGAlgorithm::IGAlgorithm");

  _ordering = OrderingSP(Ordering::create(prb, opt));
  _selector = LiteralSelector::getSelector(*_ordering, opt, opt.instGenSelection());

  _use_dm = opt.useDM();
  _use_niceness = (opt.satVarSelector() == Options::SVS_NICENESS);

  _passive.setAgeWeightRatio(_opt.ageRatio(), _opt.weightRatio());
  
  //TODO - Consider using MinimizingSolver here
  switch(opt.satSolver()){
    case Options::BUFFERED_VAMPIRE:
      _satSolver = new BufferedSolver(new TWLSolver(opt,true));
      break;
    case Options::VAMPIRE:
      _satSolver = new TWLSolver(opt,true);
      break;
    case Options::BUFFERED_LINGELING:
      _satSolver = new BufferedSolver(new LingelingInterfacing(opt,true));
      break;
    case Options::LINGELING:
      _satSolver = new LingelingInterfacing(opt,true);
      break;
    default:
      ASSERTION_VIOLATION(opt.satSolver());
  }

  _gnd = new  IGGrounder(_satSolver);

  if(_opt.globalSubsumption()) {
    _groundingIndex = new GroundingIndex(new GlobalSubsumptionGrounder(), opt);
    _globalSubsumption = new GlobalSubsumption(_groundingIndex.ptr());
  }

  _variantIdx = new ClauseVariantIndex();
  _selected = new LiteralSubstitutionTree();

  _doingSatisfiabilityCheck = false;
}

IGAlgorithm::~IGAlgorithm()
{
  CALL("IGAlgorithm::~IGAlgorithm");

  delete _selected;
  delete _variantIdx;
  delete _satSolver;
}

ClauseIterator IGAlgorithm::getActive()
{
  CALL("IGAlgorithm::getActive");

  return pvi( RCClauseStack::Iterator(_active) );
}

/**
 * Prepare the object to start solving.
 *
 * If we combine InstGen with saturation, initialize the saturation algorithm
 * with a copy of input problem.
 *
 * If equality is present in the problem, axiomatize it.
 *
 * Move problem clauses into the _inputClauses stack.
 */
void IGAlgorithm::init()
{
  CALL("IGAlgorithm::init");

  if(_opt.instGenWithResolution()) {
    _saturationIndexManager = new IndexManager(0);
    if(_opt.globalSubsumption()) {
      _saturationIndexManager->provideIndex(GLOBAL_SUBSUMPTION_INDEX, _groundingIndex.ptr());
    }

    _saturationProblem = _prb.copy(true);

    _saturationOptions = _opt;
    _saturationOptions.setSaturationAlgorithm(Options::OTTER);
//    _saturationOptions.setPropositionalToBDD(false);
//    _saturationOptions.setSplitting(Options::SM_OFF);
    _saturationAlgorithm = SaturationAlgorithm::createFromOptions(*_saturationProblem, _saturationOptions, _saturationIndexManager.ptr());

    //we will watch what clauses are derived in the
    //saturation part, so we can take advantage of them
    _saturationAlgorithm->getSimplifyingClauseContainer()->addedEvent.subscribe(this, &IGAlgorithm::onResolutionClauseDerived);

    //init the saturation algorithm run
    _saturationAlgorithm->initAlgorithmRun();
  }
  else {
    //if there's no resolution, we always do instGen
    _instGenResolutionRatio.alwaysDoFirst();
  }

  ASSERT_VALID(_prb);
  if(_prb.hasEquality()) {
    EqualityAxiomatizer ea(Options::EP_RSTC);
    ea.apply(_prb);
  }

  ClauseIterator cit = _prb.clauseIterator();

  while(cit.hasNext()) {
    Clause* cl = cit.next();
    ASS(cl->isClause());
    _inputClauses.push(cl);
  }

}

void IGAlgorithm::addClause(Clause* cl)
{
  CALL("IGAlgorithm::addClause");

  TimeCounter tc(TC_INST_GEN_SIMPLIFICATIONS);

  cl = _duplicateLiteralRemoval.simplify(cl);
  if(cl) { cl = _tautologyDeletion.simplify(cl); }
  if(cl) { cl = _trivialInequalityRemoval.simplify(cl); }
  if(!cl) {
    return;
  }

redundancy_check:
  {
    TimeCounter tc2(TC_INST_GEN_VARIANT_DETECTION);
    if(_variantIdx->retrieveVariants(cl).hasNext()) {
      cl->destroyIfUnnecessary();
      env.statistics->instGenRedundantClauses++;
      return;
    }
  }
  if (env.options->showNew()) {
    env.beginOutput();
    env.out() << "[IG] new: " << cl->toString() << std::endl;
    env.endOutput();
  }
  
  cl->incRefCnt();
  _variantIdx->insert(cl);
  if(_globalSubsumption) {
    Clause* newCl = _globalSubsumption->perform(cl);
    if(newCl!=cl) {
      ASS_L(newCl->length(), cl->length());
      ASS_G(newCl->length(), 0);

      cl = newCl;
      goto redundancy_check;
    }
  }

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
    
    if (env.options->showPassive()) {
      env.beginOutput();
      env.out() << "[IG] passive: " << cl->toString() << std::endl;
      env.endOutput();
    }

    SATClauseIterator sc = _gnd->ground(cl,_use_niceness);
    satClauses.loadFromIterator(sc);
  }
  _satSolver->ensureVarCnt(_gnd->satVarCnt());

  SATClauseIterator scit = pvi( SATClauseStack::Iterator(satClauses) );
  scit = Preprocess::removeDuplicateLiterals(scit); //this is required by the SAT solver
  
  _satSolver->addClauses(scit);

  if(_satSolver->getStatus()==SATSolver::UNSATISFIABLE) {
    Clause* foRefutation = getFORefutation(_satSolver->getRefutation());
    throw RefutationFoundException(foRefutation);
  }
}

bool IGAlgorithm::isSelected(Literal* lit)
{
  CALL("IGAlgorithm::isSelected");

  return _satSolver->trueInAssignment(_gnd->ground(lit,_use_niceness));
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

  // We check and update the dismatching constraints associated
  // with the clause being instantiated
  DismatchingLiteralIndex* dmatch;
  if(_use_dm){
    dmatch = _dismatchMap.get(isQuery? orig : otherCl);
    ASS(dmatch);
  }

  bool properInstance = false;
  unsigned clen = orig->length();
  for(unsigned i=0; i<clen; i++) {
    Literal* olit = (*orig)[i];
    Literal* glit = isQuery ? subst.applyToQuery(olit) : subst.applyToResult(olit);
    genLits.push(glit);

    // check dismatching constraint here
    // if dmatch has a generalisation of glit then we do not
    // satisfy the constraint
    // Note: the true,false options indicate checking for complement and not retrieving subs
    if(_use_dm && dmatch->getGeneralizations(glit,true,false).hasNext()){
      RSTAT_CTR_INC("dismatch blocked");
      return;
    }

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

  //Update dismatch constraints
  if(_use_dm){ dmatch->handleClause(res,true);}

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

  _selector->select(cl, selIdx);

  unsigned selCnt = cl->selected();
  for(unsigned i=0; i<selCnt; i++) {
    _selected->insert((*cl)[i], cl);
  }

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

  if(!cl->noSplits()) {
    return;
  }

  SATClauseIterator scit = _gnd->ground(cl,_use_niceness);
  scit = Preprocess::removeDuplicateLiterals(scit); //this is required by the SAT solver

  _satSolver->ensureVarCnt(_gnd->satVarCnt());
  _satSolver->addClauses(scit, true);

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
    case Statistics::SAT_SATISFIABLE:
    case Statistics::SAT_UNSATISFIABLE:
      throw;
    case Statistics::REFUTATION_NOT_FOUND:
    case Statistics::UNKNOWN:
    case Statistics::TIME_LIMIT:
    case Statistics::MEMORY_LIMIT:
      //refutation algorithm finished, we just get rid of it
      _saturationAlgorithm = 0;
      _instGenResolutionRatio.alwaysDoFirst();
      break;
    }
  }
}

void IGAlgorithm::activate(Clause* cl, bool wasDeactivated)
{
  CALL("IGAlgorithm::activate");

  selectAndAddToIndex(cl);
  
  if (env.options->showActive()) {
    env.beginOutput();
    env.out() << "[IG] active: " << cl->toString() << std::endl;
    env.endOutput();
  }
  
  // if cl does not have a dismatching index create one
  // it might already have one if it was previously deactiviated
  if(_use_dm && !_dismatchMap.find(cl)){
    RSTAT_CTR_INC("dismatch created");
    LiteralIndexingStructure * is = new LiteralSubstitutionTree();
    DismatchingLiteralIndex* dismatchIndex = new DismatchingLiteralIndex(is);
    _dismatchMap.insert(cl,dismatchIndex);
  }

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
    _deactivated.push(cl);
  }
}

void IGAlgorithm::doImmediateReactivation()
{
  CALL("IGAlgorithm::doImmediateReactivation");

  static ClauseStack toActivate;
  toActivate.reset();

  ClauseStack::Iterator dit(_deactivated);
  while(dit.hasNext()) {
    Clause* cl = dit.next();
    removeFromIndex(cl);
//    selectAndAddToIndex(cl);
    toActivate.push(cl);
  }

  _deactivated.reset();
  _deactivatedSet.reset();
  while(toActivate.isNonEmpty()) {
    Clause* cl = toActivate.pop();
    activate(cl, true);
  }
}

void IGAlgorithm::doPassiveReactivation()
{
  CALL("IGAlgorithm::doPassiveReactivation");

  static ClauseStack toActivate;
  toActivate.reset();

  RCClauseStack::DelIterator ait(_active);
  while(ait.hasNext()) {
    Clause* cl = ait.next();
    if(!_deactivatedSet.contains(cl)) {
      continue;
    }
    removeFromIndex(cl);
    _passive.add(cl);
    cl->incRefCnt(); //corresponds to addition to passive
    ait.del();
  }

  _deactivated.reset();
  _deactivatedSet.reset();
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

void IGAlgorithm::doInprocessing(RCClauseStack& clauses)
{
  CALL("IGAlgorithm::doInprocessing");

  EquivalenceDiscoverer ed(true, UINT_MAX, EquivalenceDiscoverer::CR_DEFINITIONS, false, true, true);
  UnitList* equivs = ed.getEquivalences(pvi(RCClauseStack::Iterator(clauses)));

  if(!equivs) {
    return;
  }

  PDInliner pdi;
  pdi.scanAndRemoveDefinitions(equivs, false);

  RCClauseStack::DelIterator cit(clauses);
  while(cit.hasNext()) {
    Clause* cl = cit.next();
    Unit* aplResU = pdi.apply(cl);
    if(!aplResU) {
      cl->decRefCnt();
      cit.del();
    }
    else {
      ASS(aplResU->isClause());
      Clause* aplRes = static_cast<Clause*>(aplResU);
      if(aplRes!=cl) {
	cl->decRefCnt();
	aplRes->incRefCnt();
	cit.replace(aplRes);
      }
    }
  }
}

void IGAlgorithm::restartWithCurrentClauses()
{
  CALL("IGAlgorithm::restartWithCurrentClauses");

  static RCClauseStack allClauses;
  allClauses.reset();

  while(_active.isNonEmpty()) {
    allClauses.pushWithoutInc(_active.popWithoutDec());
  }
  while(!_passive.isEmpty()) {
    allClauses.pushWithoutInc(_passive.popSelected());
  }
  while(_unprocessed.isNonEmpty()) {
    allClauses.pushWithoutInc(_unprocessed.popWithoutDec());
  }

  wipeIndexes();

  if(!_doingSatisfiabilityCheck && _opt.instGenInprocessing()) {
    doInprocessing(allClauses);
  }

  while(allClauses.isNonEmpty()) {
    Clause* cl = allClauses.popWithoutDec();
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

  RCClauseStack::Iterator icit(_inputClauses);
  while(icit.hasNext()) {
    Clause* cl = icit.next();
    if(isRefutation(cl)) {
      throw RefutationFoundException(cl);
    }
    addClause(cl);
  }

  int restartRatioMultiplier = 100;
  int bigRestartRatio = static_cast<int>(restartRatioMultiplier * _opt.instGenBigRestartRatio());
  int smallRestartRatio = restartRatioMultiplier - bigRestartRatio;

  int restartKindRatio = 0;

  unsigned loopIterBeforeRestart = _opt.instGenRestartPeriod();

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
      if(restarting) {
	// if we activate more than instGenRestartPeriod clauses then we 'restart'
        // what does this entail?
	break;
      }

      if(_opt.instGenPassiveReactivation()) {
	doPassiveReactivation();
      }
      else {
	doImmediateReactivation();
      }


      while(_instGenResolutionRatio.shouldDoSecond()) {
	_instGenResolutionRatio.doSecond();
	doResolutionStep();
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
	  loopIterBeforeRestart*_opt.instGenRestartPeriodQuotient()));

    }
    else {
      //we're here because there were no more clauses to activate
      restartWithCurrentClauses();
      _doingSatisfiabilityCheck = true;
      processUnprocessed();
      while(!_passive.isEmpty() && _unprocessed.isEmpty()) {
        Clause* given = _passive.popSelected();
        activate(given);
      }
      _doingSatisfiabilityCheck = false;
      if(_unprocessed.isEmpty()) {
        return onModelFound();
      }
    }
  }
}

MainLoopResult IGAlgorithm::onModelFound()
{
  CALL("IGAlgorithm::onModelFound");

  if(_opt.complete(_prb)) {
    MainLoopResult res(Statistics::SATISFIABLE);
    if(_opt.proof()!=Options::PROOF_OFF) {
      //we need to print this early because model generating can take some time
      if(UIHelper::cascMode) {
	env.beginOutput();
	env.out() << "% SZS status "<<( UIHelper::haveConjecture() ? "CounterSatisfiable" : "Satisfiable" )
	    << " for " << _opt.problemName() << endl << flush;
	env.endOutput();
	UIHelper::satisfiableStatusWasAlreadyOutput = true;
      }


      vostringstream modelStm;
      bool modelAvailable = ModelPrinter(*this).tryOutput(modelStm);
      if(modelAvailable) {
	env.statistics->model = modelStm.str();
      }
      else {
	res.saturatedSet = 0;
	UnitList::pushFromIterator( RCClauseStack::Iterator(_active) , res.saturatedSet);
      }
    }
    return res;
  }
  else {
    return MainLoopResult(Statistics::REFUTATION_NOT_FOUND);
  }
}

}
