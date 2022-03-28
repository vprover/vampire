/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file IGAlgorithm.cpp
 * Implements class IGAlgorithm.
 */

#include <cmath>
#include <sstream>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/System.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"
#include "Lib/ScopedLet.hpp"
#include "Lib/Timer.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/RCClauseStack.hpp"
#include "Kernel/SortHelper.hpp"

#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/LiteralIndex.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/MinisatInterfacing.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Property.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "IGAlgorithm.hpp"
#include "ModelPrinter.hpp"

#undef LOGGING
#define LOGGING 0

#define VTRACE_DM 0

namespace InstGen
{

using namespace Indexing;
using namespace Saturation;

static const int LOOKAHEAD_SELECTION = 1011;

IGAlgorithm::IGAlgorithm(Problem& prb,const Options& opt)
: MainLoop(prb, opt),
    _instGenResolutionRatio(opt.instGenResolutionRatioInstGen(),
	opt.instGenResolutionRatioResolution(), 50),
    _passive(opt),
    _tautologyDeletion(false),
    _equalityProxy(0)
{
  CALL("IGAlgorithm::IGAlgorithm");

  _ordering = OrderingSP(Ordering::create(prb, opt));

  if (opt.instGenSelection() == LOOKAHEAD_SELECTION) {
    _doLookahead = true;
  } else {
    _doLookahead = false;
    _selector = LiteralSelector::getSelector(*_ordering, opt, opt.instGenSelection());
  }

  // _use_dm = opt.useDM();

  _passive.setAgeWeightRatio(_opt.ageRatio(), _opt.weightRatio());

  //TODO - Consider using MinimizingSolver here
  switch(opt.satSolver()){
    case Options::SatSolver::MINISAT:
      _satSolver = new MinisatInterfacing(opt,true);
      break;
#if VZ3
    case Options::SatSolver::Z3:
      //cout << "Warning: Z3 not compatible with inst_gen, using Minisat" << endl;
      _satSolver = new MinisatInterfacing(opt,true);
      break;
#endif
    default:
      ASSERTION_VIOLATION_REP(opt.satSolver());
  }

  // TODO: should instgen use buffering?

  _gnd = new  IGGrounder(_satSolver);

  if(_opt.globalSubsumption()) {
    _groundingIndex = new GroundingIndex(opt);
    _globalSubsumption = new GlobalSubsumption(_opt,_groundingIndex.ptr());
  }

  _use_hashing = _opt.useHashingVariantIndex();
  if (_use_hashing) {
    _variantIdx = new HashingClauseVariantIndex();
  } else {
    _variantIdx = new SubstitutionTreeClauseVariantIndex();
  }
  _selected = new LiteralSubstitutionTree();

  _doingSatisfiabilityCheck = false;
}

IGAlgorithm::~IGAlgorithm()
{
  CALL("IGAlgorithm::~IGAlgorithm");

  delete _selected;
  delete _variantIdx;
  delete _satSolver;
  if (_equalityProxy) {
    delete _equalityProxy;
  }
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
    _saturationOptions.setSaturationAlgorithm(Options::SaturationAlgorithm::DISCOUNT);
    _saturationOptions.setAgeRatio(7);
    _saturationOptions.setWeightRatio(1);
    _saturationOptions.setSelection(11);
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
    _equalityProxy = new EqualityProxyMono(Options::EqualityProxy::RSTC);
    _equalityProxy->apply(_prb);
  }

  ClauseIterator cit = _prb.clauseIterator();

  while(cit.hasNext()) {
    Clause* cl = cit.next();
    ASS(cl->isClause());
    _inputClauses.push(cl);
  }
}

bool IGAlgorithm::addClause(Clause* cl)
{
  CALL("IGAlgorithm::addClause");

  TimeCounter tc(TC_INST_GEN_SIMPLIFICATIONS);

  cl = _duplicateLiteralRemoval.simplify(cl);
  if(cl) { cl = _tautologyDeletion.simplify(cl); }
  if(cl) { cl = _trivialInequalityRemoval.simplify(cl); }
  if(cl) { cl = _distinctEqualitySimplifier.simplify(cl); }
  if(!cl) {
    return false;
  }

redundancy_check:
  {
    bool redundant;
    {
      TimeCounter tc2(TC_INST_GEN_VARIANT_DETECTION);
      redundant = _variantIdx->retrieveVariants(cl).hasNext();
    }
    if (redundant) {
      cl->destroyIfUnnecessary();
      env.statistics->instGenRedundantClauses++;
      return false;
    }
  }
  if (env.options->showNew()) {
    env.beginOutput();
    env.out() << "[IG] new: " << cl->toString() << std::endl;
    env.endOutput();
  }

  if(_globalSubsumption) {
    static Stack<Unit*> prems_dummy;
    
    Clause* newCl = _globalSubsumption->perform(cl,prems_dummy);
    if(newCl!=cl) {
      ASS_L(newCl->length(), cl->length());
      
      if (newCl->length() == 0) {
        // A future integration of instgen with AVATAR should consider the case
        // of conditional empty clause
        throw RefutationFoundException(newCl);
      }
                  
      cl = newCl;
      goto redundancy_check;
    }
  }

  cl->incRefCnt();
  _variantIdx->insert(cl);

  _unprocessed.push(cl);
  env.statistics->instGenKeptClauses++;
  return true;
}

Clause* IGAlgorithm::getFORefutation(SATClause* satRefutation, SATClauseList* satPremises)
{
  CALL("IGAlgorithm::getFORefutation");
  ASS(satRefutation);

  UnitList* prems = SATInference::getFOPremises(satRefutation);

  Inference foInf(FromSatRefutation(InferenceRule::SAT_INSTGEN_REFUTATION, prems,
          // satPremises may be nullptr already, if our solver does not support minimization
          env.options->minimizeSatProofs() ? satPremises : nullptr));

  Clause* foRef = Clause::fromIterator(LiteralIterator::getEmpty(), foInf);
  return foRef;
}

void IGAlgorithm::processUnprocessed()
{
  CALL("IGAlgorithm::processUnprocessed");

  TimeCounter tc(TC_INST_GEN_SAT_SOLVING);

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

    SATClause* sc = _gnd->ground(cl);
    sc = SATClause::removeDuplicateLiterals(sc); //this is required by the SAT solver

    // sc could have been a tautology, in which case sc == 0 after the removeDuplicateLiterals call
    if (sc) {
      _satSolver->addClause(sc);
    }
  }

  if(_satSolver->solve()==SATSolver::UNSATISFIABLE) {
    Clause* foRefutation = getFORefutation(_satSolver->getRefutation(),_satSolver->getRefutationPremiseList());
    throw RefutationFoundException(foRefutation);
  }
}

bool IGAlgorithm::isSelected(Literal* lit)
{
  CALL("IGAlgorithm::isSelected");

  return _satSolver->trueInAssignment(_gnd->groundLiteral(lit));
}

/**
 * Instantiate literals of @c orig using substitution @c subst,
 * and store the instance literals in genLits.
 * Either query or result part of the substitution @c subst is used, based on the
 * value of @c isQuery.
 *
 * Returns false if the generation of the clause was blocked due to dismatching constraints.
 * Even if true is returned, @c properInstance can still be set to false,
 * if the subst is not a proper instantiator of orig,
 * in which case the clause generation should be abandoned.
 */
bool IGAlgorithm::startGeneratingClause(Clause* orig, ResultSubstitution& subst, bool isQuery, Clause* otherCl,Literal* origLit, LiteralStack& genLits, bool& properInstance)
{
  CALL("IGAlgorithm::startGeneratingClause");

#if VTRACE_DM
  cout << "tryGenC " << orig->number() << " and " << otherCl->number() << " on " << origLit->toString() << endl;
#endif

  genLits.reset();

  /*
  // We check and update the dismatching constraints associated
  // with the clause being instantiated
  DismatchingContraints* dmatch = 0;
  if(_use_dm){
    TimeCounter tc(TC_DISMATCHING);
    _dismatchMap.find(orig,dmatch);
  }
  */

  unsigned clen = orig->length();
  Literal* origLitGnd = 0;
  for(unsigned i=0; i<clen; i++) {
    Literal* olit = (*orig)[i];
    Literal* glit = isQuery ? subst.applyToQuery(olit) : subst.applyToResult(olit);

    if (olit == origLit) {
      origLitGnd = glit;
    }

    /*
    {
      TimeCounter tc(TC_DISMATCHING);
      // check dismatching constraint here
      if (dmatch && dmatch->shouldBlock(olit,glit)) {
        RSTAT_CTR_INC("dismatch blocked");
#if VTRACE_DM
        cout << "[" << dmatch << "] " << "blocking for " << orig->number() << " and " << glit->toString() << endl;
        cout << "block with origLit : " << (olit==origLit) << endl;
#endif
        return false;
      }
    }
    */

    genLits.push(glit);
  }

  ASS_NEQ(origLitGnd,0);
  SATLiteral oLitSat = _gnd->groundLiteral(origLit);
  SATLiteral gLitSat = _gnd->groundLiteral(origLitGnd);

  properInstance = (oLitSat!=gLitSat);

  return true;
}

/**
 * Finish generating the clause started in startGeneratingClause, also updating dismatching constraints of orig if applicable.
 */
void IGAlgorithm::finishGeneratingClause(Clause* orig, ResultSubstitution& subst, bool isQuery, Clause* otherCl,Literal* origLit, LiteralStack& genLits)
{
  CALL("IGAlgorithm::finishGeneratingClause");

  Clause* res = Clause::fromStack(genLits, GeneratingInference1(InferenceRule::INSTANCE_GENERATION, orig));
  // make age also depend on the age of otherCl
  res->setAge(max(orig->age(), otherCl->age())+1);

  env.statistics->instGenGeneratedClauses++;
  bool added = addClause(res);
  (void)added;

  /*
  //Update dismatch constraints
  if(added && _use_dm) {
    TimeCounter tc(TC_DISMATCHING);

    DismatchingContraints* dmatch = 0;

    // if dmatch does not exist create it 
    if(!_dismatchMap.find(orig,dmatch)) {
      RSTAT_CTR_INC("dismatch created");

      dmatch = new DismatchingContraints();
      ALWAYS(_dismatchMap.insert(orig,dmatch));
#if VTRACE_DM
      cout << "[" << dmatch << "] "<< "creating for " << orig->toString() << endl;
#endif
    }

    Literal* dm_with = isQuery ? subst.applyToQuery(origLit) : subst.applyToResult(origLit);
#if VTRACE_DM
      cout << "[" << dmatch << "] "<< "dismatch " << orig->number() << " add " << dm_with->toString() << endl;
#endif
    dmatch->add(origLit,dm_with);
  }
  */
}

/**
 * Generate instances from literal of index @c litIdx in clause @c cl,
 * using the selected literals in @c selected index.
 */
void IGAlgorithm::tryGeneratingInstances(Clause* cl, unsigned litIdx)
{
  CALL("IGAlgorithm::tryGeneratingInstances");

  TimeCounter tc(TC_INST_GEN_GEN_INST);

  Literal* lit = (*cl)[litIdx];

  SLQueryResultIterator unifs = _selected->getUnifications(lit, true, true);
  while(unifs.hasNext()) {
    SLQueryResult unif = unifs.next();
    if(!isSelected(unif.literal)) {
      deactivate(unif.clause);
      continue;//literal is no longer selected
    }

    static LiteralStack genLits1;
    static LiteralStack genLits2;
    bool properInstance1;
    bool properInstance2;

    if (startGeneratingClause(cl, *unif.substitution, true, unif.clause,lit,genLits1,properInstance1) &&
        startGeneratingClause(unif.clause, *unif.substitution, false, cl,unif.literal,genLits2,properInstance2)) {

      // dismatching test passed for both

      if(unif.clause->length()==1) {
        //we make sure the unit is added first, so that it can be used to shorten the
        //second clause by global subsumption
        if (properInstance2) {
          finishGeneratingClause(unif.clause, *unif.substitution, false, cl,unif.literal,genLits2);
        }
        if (properInstance1) {
          finishGeneratingClause(cl, *unif.substitution, true, unif.clause,lit,genLits1);
        }
      } else {
        if (properInstance1) {
          finishGeneratingClause(cl, *unif.substitution, true, unif.clause,lit,genLits1);
        }
        if (properInstance2) {
          finishGeneratingClause(unif.clause, *unif.substitution, false, cl,unif.literal,genLits2);
        }
      }
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
 * Select literals in cl by trying to estimate
 * how many inferences the particular selection
 * would lead in the next step.
 */
unsigned IGAlgorithm::lookaheadSelection(Clause* cl, unsigned selCnt)
{
  CALL("IGAlgorithm::lookaheadSelection");

  static DArray<VirtualIterator<SLQueryResult>> iters; //IG unification iterators
  iters.ensure(selCnt);

  for(unsigned i=0; i<selCnt; i++) {
    iters[i] = pvi(getFilteredIterator(_selected->getUnifications((*cl)[i], true, false),
        // only count partner literals which are also semantically selected
        [this](SLQueryResult& unif) { return isSelected(unif.literal); }));
  }

  static Stack<unsigned> candidates; // just to make sure we break the ties in a fair way
  candidates.reset();
  do {
    for(unsigned i=0;i<selCnt;i++) {
      if(iters[i].hasNext()) {
        iters[i].next();
      }
      else {
        candidates.push(i);
      }
    }
  } while(candidates.isEmpty());

  // candidates are in ascending order

  //release the iterators
  for(unsigned i=0;i<selCnt;i++) {
    iters[i].drop();
  }

  // UPDATE THE SELECTION
  unsigned selIdx = 0;

  // for now, take all the tied ones
  for (unsigned i=0; i < candidates.size(); i++) {
    unsigned idx = candidates[i];
    if(selIdx!=idx) {
      swap((*cl)[idx], (*cl)[selIdx]);
    }
    selIdx++;
  }
  return selIdx;
}

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

  if (_doLookahead) {
    unsigned selCnt = selIdx>1 ? lookaheadSelection(cl,selIdx) : 1;
    cl->setSelected(selCnt);
  } else {
    _selector->select(cl, selIdx);
  }

  unsigned selCnt = cl->numSelected();
  ASS_GE(selCnt,1);
  for(unsigned i=0; i<selCnt; i++) {
    _selected->insert((*cl)[i], cl);
  }
}

void IGAlgorithm::removeFromIndex(Clause* cl)
{
  CALL("IGAlgorithm::removeFromIndex");

  unsigned selCnt = cl->numSelected();
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

  if (_equalityProxy) { // we had equality in the problem
    cl = _equalityProxy->apply(cl);
  }

  SATClause* sc = _gnd->ground(cl);
  sc = SATClause::removeDuplicateLiterals(sc); //this is required by the SAT solver

  // sc could have been a tautology, in which case sc == 0 after the removeDuplicateLiterals call
  if (sc) {
    _satSolver->addClause(sc);
  }

  if(_satSolver->solve(true)==SATSolver::UNSATISFIABLE) {
    Clause* foRefutation = getFORefutation(_satSolver->getRefutation(),_satSolver->getRefutationPremiseList());
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
    ScopedLet<Options*> optLet(env.options,&_saturationOptions);
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
    case Statistics::INAPPROPRIATE:
    case Statistics::TIME_LIMIT:
    case Statistics::MEMORY_LIMIT:
    case Statistics::ACTIVATION_LIMIT:
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
  if (_use_hashing) {
    _variantIdx = new HashingClauseVariantIndex();
  } else {
    _variantIdx = new SubstitutionTreeClauseVariantIndex();
  }
  _selected = new LiteralSubstitutionTree();
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

  while(allClauses.isNonEmpty()) {
    Clause* cl = allClauses.popWithoutDec();
    addClause(cl);
    cl->decRefCnt();//corresponds to the removal from the active and passive container
  }
}

void IGAlgorithm::restartFromBeginning()
{
  CALL("IGAlgorithm::restartFromBeginning");

  /*
  {
    TimeCounter tc(TC_DISMATCHING);
    // throw away dismatching constraints
    DismatchMap::Iterator iit(_dismatchMap);
    while(iit.hasNext()){ delete iit.next(); }
    _dismatchMap.reset();
  }
  */

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
      // ASS_EQ(_satSolver->getStatus(), SATSolver::SATISFIABLE);

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
    if(_opt.proof()!=Options::Proof::OFF) {
      //we need to print this early because model generating can take some time
      reportSpiderStatus('-');
      if(szsOutputMode()) {
        env.beginOutput();
        env.out() << "% SZS status "<<( UIHelper::haveConjecture() ? "CounterSatisfiable" : "Satisfiable" )
            << " for " << _opt.problemName() << endl << flush;
        env.endOutput();
        UIHelper::satisfiableStatusWasAlreadyOutput = true;
      }

      // Prevent timing out whilst the model is being printed
      Timer::setLimitEnforcement(false);

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
