/**
 * @file SSplitter.cpp
 * Implements class SSplitter.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RCClauseStack.hpp"
#include "Kernel/TermIterators.hpp"

#include "Shell/Options.hpp"
#include "Shell/Refutation.hpp"
#include "Shell/Statistics.hpp"

#include "SAT/Preprocess.hpp"
#include "SAT/SATInference.hpp"
#include "SAT/TWLSolver.hpp"
#include "SAT/MinimizingSolver.hpp"

#include "SSplitter.hpp"
#include "SaturationAlgorithm.hpp"


#define DEBUG_MIN_SOLVER VDEBUG

#if DEBUG_MIN_SOLVER
#include "Test/CheckedSatSolver.hpp"
#endif

namespace Saturation
{

using namespace Lib;
using namespace Kernel;


/////////////////////////////
// SSplittingBranchSelector
//

void SSplittingBranchSelector::init()
{
  CALL("SSplittingBranchSelector::init");

  _eagerRemoval = _parent.getOptions().ssplittingEagerRemoval();
//  _sweepingMode = _parent.getOptions().ssplittingComponentSweeping();

  _solver = new MinimizingSolver(new TWLSolver(_parent.getOptions(), true));
#if DEBUG_MIN_SOLVER
  _solver = new Test::CheckedSatSolver(_solver.release());
#endif
}

void SSplittingBranchSelector::updateVarCnt()
{
  CALL("SSplittingBranchSelector::ensureVarCnt");

  unsigned satVarCnt = _parent.maxSatVar()+1;
  unsigned splitLvlCnt = _parent.splitLevelCnt();

  LOG("sspl_var_cnt","ensuring varCnt to "<<satVarCnt);
  _solver->ensureVarCnt(satVarCnt);
  _selected.expand(splitLvlCnt);
//  _watcher.expand(varCnt);
}

//bool SSplittingBranchSelector::hasPositiveLiteral(SATClause* cl)
//{
//  CALL("SSplittingBranchSelector::hasPositiveLiteral");
//
//  SATClause::Iterator it(*cl);
//  while(it.hasNext()) {
//    SATLiteral l = it.next();
//    if(l.isPositive()) { return true; }
//  }
//  return false;
//}
//
//bool SSplittingBranchSelector::isSatisfiedBySelection(SATLiteral lit)
//{
//  CALL("SSplittingBranchSelector::isSatisfiedBySelection");
//
//  return lit.polarity()==_selected.find(lit.var());
//}
//
void SSplittingBranchSelector::handleSatRefutation(SATClause* ref)
{
  CALL("SSplittingBranchSelector::handleSatRefutation");

  UnitList* prems = SATInference::getFOPremises(ref);
  Inference* foInf = new InferenceMany(Inference::SPLITTING, prems);
  Clause* foRef = Clause::fromIterator(LiteralIterator::getEmpty(), Unit::CONJECTURE, foInf);
  throw MainLoop::RefutationFoundException(foRef);
}

void SSplittingBranchSelector::updateSelection(unsigned satVar, SATSolver::VarAssignment asgn,
    SplitLevelStack& addedComps, SplitLevelStack& removedComps)
{
  CALL("SSplittingBranchSelector::updateSelection");
  ASS_NEQ(asgn, SATSolver::NOT_KNOWN); //we always do full SAT solving, so there shouldn't be unknown variables

  SplitLevel posLvl = _parent.getNameFromLiteral(SATLiteral(satVar, true));
  SplitLevel negLvl = _parent.getNameFromLiteral(SATLiteral(satVar, false));

  switch(asgn) {
  case SATSolver::TRUE:
    if(!_selected.find(posLvl) && _parent.isActiveName(posLvl)) {
      _selected.insert(posLvl);
      addedComps.push(posLvl);
    }
    if(_selected.find(negLvl)) {
      _selected.remove(negLvl);
      removedComps.push(negLvl);
    }
    break;
  case SATSolver::FALSE:
    if(!_selected.find(negLvl) && _parent.isActiveName(negLvl)) {
      _selected.insert(negLvl);
      addedComps.push(negLvl);
    }
    if(_selected.find(posLvl)) {
      _selected.remove(posLvl);
      removedComps.push(posLvl);
    }
    break;
  case SATSolver::DONT_CARE:
    if(_eagerRemoval) {
      if(_selected.find(posLvl)) {
        _selected.remove(posLvl);
        removedComps.push(posLvl);
      }
      if(_selected.find(negLvl)) {
        _selected.remove(negLvl);
        removedComps.push(negLvl);
      }
    }
    break;
  default:
    ASSERTION_VIOLATION;
  }

}

void SSplittingBranchSelector::addSatClauses(const SATClauseStack& clauses,
    SplitLevelStack& addedComps, SplitLevelStack& removedComps)
{
  CALL("SSplittingBranchSelector::addSatClauses");
  ASS(addedComps.isEmpty());
  ASS(removedComps.isEmpty());

  TimeCounter tc(TC_SPLITTING_COMPONENT_SELECTION);

//  _unprocessed.loadFromIterator(
//      getFilteredIterator(SATClauseStack::ConstIterator(clauses), hasPositiveLiteral) );

  RSTAT_CTR_INC_MANY("ssat_sat_clauses",clauses.size());
//  RSTAT_CTR_INC_MANY("ssat_sat_clauses_with_positive",_unprocessed.size());

  TRACE("sspl_sat_clauses",
      SATClauseStack::ConstIterator cit(clauses);
      while(cit.hasNext()) {
	tout << (*cit.next()) << endl;
      }
  );

  {
    TimeCounter tc1(TC_SAT_SOLVER);
    _solver->addClauses(pvi( SATClauseStack::ConstIterator(clauses) ), false);
  }

  if(_solver->getStatus()==SATSolver::UNSATISFIABLE) {
    LOG("sspl_sel","cannot fix selection, refutation found");
    SATClause* satRefutation = _solver->getRefutation();
    handleSatRefutation(satRefutation);
  }
  ASS_EQ(_solver->getStatus(),SATSolver::SATISFIABLE);

  unsigned maxSatVar = _parent.maxSatVar();
  for(unsigned i=1; i<=maxSatVar; i++) {
    SATSolver::VarAssignment asgn = _solver->getAssignment(i);
    updateSelection(i, asgn, addedComps, removedComps);
  }

//
//
//
//  deselectByModel(removedComps);
//  fixUnprocessed(addedComps);
//
//  sweep(addedComps, removedComps);

  COND_LOG("sspl_sel",addedComps.isNonEmpty()||removedComps.isNonEmpty(), "selection changed by addition of SAT clauses");
  COND_TRACE("sspl_sel_added",addedComps.isNonEmpty(),
      tout << "added:" << endl;
      SplitLevelStack::Iterator cit(addedComps);
      while(cit.hasNext()) {
	SplitLevel var = cit.next();
	tout << "  " << var << "  --  " << (*_parent.getComponentClause(var)) << endl;
      }
  );
  COND_TRACE("sspl_sel_removed",removedComps.isNonEmpty(),
      tout << "removed:" << endl;
      SplitLevelStack::Iterator cit(removedComps);
      while(cit.hasNext()) {
	SplitLevel var = cit.next();
	tout << "  " << var << "  --  " << (*_parent.getComponentClause(var)) << endl;
      }
  );
  RSTAT_CTR_INC_MANY("ssat_usual_activations", addedComps.size());
  RSTAT_CTR_INC_MANY("ssat_usual_deactivations", removedComps.size());

}

/**
 * Switch to a different splitting branch
 */
void SSplittingBranchSelector::flush(SplitLevelStack& addedComps, SplitLevelStack& removedComps)
{
  CALL("SSplittingBranchSelector::flush");
  ASS(addedComps.isEmpty());
  ASS(removedComps.isEmpty());

  SplitLevel varCnt = _parent.maxSatVar()+1;

  static ArraySet oldselSet;
  oldselSet.ensure(varCnt);
  oldselSet.reset();

#if 0 //old flushing code
  //this we do to change the model in the SAT solver
  ArraySet::Iterator sit(_selected);
  while(sit.hasNext()) {
    SplitLevel sel = sit.next();
    if(_solver->getStatus()==SATSolver::UNSATISFIABLE) {
      _solver->retractAllAssumptions();
    }
    _solver->addAssumption(_parent.getLiteralFromName(sel).opposite(), true);
  }
  _solver->retractAllAssumptions();
  //restore model
  _solver->addClauses(SATClauseIterator::getEmpty(), false);
#else
  if(_solver->getStatus()==SATSolver::UNKNOWN) {
    _solver->addClauses(SATClauseIterator::getEmpty(), false);
  }
  _solver->addClauses(SATClauseIterator::getEmpty(), false);
  ASS_EQ(_solver->getStatus(), SATSolver::SATISFIABLE);
  _solver->randomizeAssignment();
#endif
  ASS_EQ(_solver->getStatus(), SATSolver::SATISFIABLE);

  unsigned maxSatVar = _parent.maxSatVar();
  for(unsigned i=1; i<=maxSatVar; i++) {
    SATSolver::VarAssignment asgn = _solver->getAssignment(i);
    updateSelection(i, asgn, addedComps, removedComps);
  }

  RSTAT_CTR_INC_MANY("ssat_added_by_flush",addedComps.size());
  RSTAT_CTR_INC_MANY("ssat_removed_by_flush",removedComps.size());
  COND_LOG("sspl_sel",addedComps.isNonEmpty()||removedComps.isNonEmpty(), "flushing changed by addition of SAT clauses");
  COND_TRACE("sspl_sel_added",addedComps.isNonEmpty(),
      tout << "added:" << endl;
      SplitLevelStack::Iterator cit(addedComps);
      while(cit.hasNext()) {
	SplitLevel var = cit.next();
	tout << "  " << var << "  --  " << (*_parent.getComponentClause(var)) << endl;
      }
  );
  COND_TRACE("sspl_sel_removed",removedComps.isNonEmpty(),
      tout << "removed:" << endl;
      SplitLevelStack::Iterator cit(removedComps);
      while(cit.hasNext()) {
	SplitLevel var = cit.next();
	tout << "  " << var << "  --  " << (*_parent.getComponentClause(var)) << endl;
      }
  );
}

//void SSplittingBranchSelector::select(SplitLevel var)
//{
//  CALL("SSplittingBranchSelector::select");
//  ASS(!_selected.find(var));
//  ASS(!_solver->getAssignment(var).isFalse());
//
//  _selected.insert(var);
//  SATClauseStack& watched = _watcher[var];
//  _unprocessed.loadFromIterator(SATClauseStack::Iterator(watched));
//  watched.reset();
//}
//
//void SSplittingBranchSelector::deselectByModel(SplitLevelStack& removedComps)
//{
//  CALL("SSplittingBranchSelector::deselectByModel");
//  ASS_EQ(_solver->getStatus(), SATSolver::SATISFIABLE);
//
//  static SplitLevelStack toDeselect;
//  toDeselect.reset();
//
//  ArraySet::Iterator sit(_selected);
//  while(sit.hasNext()) {
//    unsigned sel = sit.next();
//    if(_solver->getAssignment(sel)==false) {
//      toDeselect.push(sel);
//    }
//  }
//
//  RSTAT_CTR_INC_MANY("ssat_deselected_by_model",toDeselect.size());
//  while(toDeselect.isNonEmpty()) {
//    unsigned sel = toDeselect.pop();
//    removedComps.push(sel);
//    _selected.remove(sel);
//    SATClauseStack& watched = _watcher[sel];
//    _unprocessed.loadFromIterator(SATClauseStack::Iterator(watched));
//    RSTAT_CTR_INC_MANY("ssat_sat_clauses_invalidated_by_model_deselection",watched.size());
//    watched.reset();
//  }
//}
//
//void SSplittingBranchSelector::fixUnprocessed(SplitLevelStack& addedComps)
//{
//  CALL("SSplittingBranchSelector::fixUnprocessed");
//
//  while(_unprocessed.isNonEmpty()) {
//    SATClause* cl = _unprocessed.pop();
//    if(tryAddingToWatch(cl)) { continue; }
//    SplitLevel toSelect = getVarToSelect(cl);
//    addedComps.push(toSelect);
//    select(toSelect);
//    _watcher[toSelect].push(cl);
//    RSTAT_CTR_INC("ssat_activations_in_unprocessed_fixing");
//  }
//}
//
//bool SSplittingBranchSelector::tryAddingToWatch(SATClause* cl)
//{
//  CALL("SSplittingBranchSelector::tryAddingToWatch");
//
//  //TODO: pick smartly watch to add to
//  SATClause::Iterator it(*cl);
//  while(it.hasNext()) {
//    SATLiteral lit = it.next();
//    if(isSatisfiedBySelection(lit)) {
//      SplitLevel var = lit.var();
//      _watcher[var].push(cl);
//      return true;
//    }
//  }
//  return false;
//}
//
//SplitLevel SSplittingBranchSelector::getVarToSelect(SATClause* cl)
//{
//  CALL("SSplittingBranchSelector::getVarToSelect");
//
//  static SplitLevelStack eligible;
//  eligible.reset();
//
//  SATClause::Iterator it(*cl);
//  while(it.hasNext()) {
//    SATLiteral lit = it.next();
//    SplitLevel var = lit.var();
//    if(!lit.polarity()) {
//      //clause should be unsatisfied, therefore negative literals must be selected
//      ASS(_selected.find(var));
//      continue;
//    }
//    ASS(!_selected.find(var)); //clause should be unsatisfied
//    if(_solver->getAssignment(var)==false) { continue; }
//
//    eligible.push(var);
//  }
//  ASS_G(eligible.size(),0);
//  if(eligible.size()==1) {
//    return eligible.top();
//  }
//
//  //TODO: pick smartly the literal to select
//  return *std::min_element(eligible.begin(), eligible.end());
//}
//
//bool SSplittingBranchSelector::hasAlternativeSelection(SATClause* cl, SplitLevel forbidden)
//{
//  CALL("SSplittingBranchSelector::hasAlternativeSelection");
//  ASS(_selected.find(forbidden));
//
//  SATClause::Iterator it(*cl);
//  while(it.hasNext()) {
//    SATLiteral l = it.next();
//    if(l.var()==forbidden) {
//      ASS(l.polarity());
//      continue;
//    }
//    if(isSatisfiedBySelection(l)) {
//      return true;
//    }
//  }
//  return false;
//}
//
//template<class It>
//void SSplittingBranchSelector::sweepVars(It varsToSweep, SplitLevelStack& sweptAway)
//{
//  CALL("SSplittingBranchSelector::sweepVars");
//
//  while(varsToSweep.hasNext()) {
//    SplitLevel var = varsToSweep.next();
//    if(!_selected.find(var)) {
//      //the variable is already non-selected
//      continue;
//    }
//    SATClauseStack& watched = _watcher[var];
//    SATClauseStack::Iterator wit1(watched);
//    bool canDeselect = true;
//    while(wit1.hasNext()) {
//      SATClause* cl = wit1.next();
//      if(!hasAlternativeSelection(cl, var)) {
//	canDeselect = false;
//	break;
//      }
//    }
//    if(!canDeselect) {
//      continue;
//    }
//    //now we know each of the watched clauses can be moved to another watch
//    RSTAT_CTR_INC("ssat_deactivated_by_sweeping");
//    RSTAT_CTR_INC_MANY("ssat_sat_clauses_moved_by_sweeping",watched.size());
//    LOG("sspl_sel_swept","swept component from selected: "<<var<<" -- "<<(*_parent.getComponentClause(var)));
//    sweptAway.push(var);
//    _selected.remove(var);
//    while(watched.isNonEmpty()) {
//      SATClause* cl = watched.pop();
//#if VDEBUG
//      unsigned wsize = watched.size();
//#endif
//      //we have earlier checked that the clause can be moved to another watch
//      ALWAYS(tryAddingToWatch(cl));
//      ASS_EQ(watched.size(),wsize); //we assert that the clause didn't appear back in the old watch
//    }
//  }
//}
//
//void SSplittingBranchSelector::sweep(SplitLevelStack& addedComps, SplitLevelStack& removedComps)
//{
//  CALL("SSplittingBranchSelector::sweep");
//
//  if(_sweepingMode==Options::SSCS_NONE) {
//    return;
//  }
//
//  static SplitLevelStack sweptAway;
//  sweptAway.reset();
//
//  sweepVars(SplitLevelStack::Iterator(addedComps), sweptAway);
//
//  if(_sweepingMode!=Options::SSCS_ONLY_NEW) {
//
//    unsigned sweptSz = sweptAway.size();
//    sweepVars(getRangeIterator((SplitLevel)1, (SplitLevel)_watcher.size()), sweptAway);
//    if(_sweepingMode==Options::SSCS_ITERATED) {
//      while (sweptSz<sweptAway.size()) {
//	sweptSz = sweptAway.size();
//	sweepVars(getRangeIterator((SplitLevel)1, (SplitLevel)_watcher.size()), sweptAway);
//	RSTAT_CTR_INC("ssat_sweeping_reiteration");
//	RSTAT_CTR_INC_MANY("ssat_sweeping_reiteration_added",sweptAway.size()-sweptSz);
//      }
//    }
//    else {
//      ASS_EQ(_sweepingMode,Options::SSCS_ALL);
//    }
//  }
//
//  if(sweptAway.isEmpty()) {
//    return;
//  }
//
//  static ArraySet sweptSet;
//  sweptSet.ensure(_watcher.size());
//
//  //first we put new components into the varsSet to determine which old components were removed
//  sweptSet.reset();
//  sweptSet.insertFromIterator(SplitLevelStack::Iterator(sweptAway));
//
//  SplitLevelStack::StableDelIterator ait(addedComps);
//  while(ait.hasNext()) {
//    SplitLevel v = ait.next();
//    if(sweptSet.find(v)) {
//      RSTAT_CTR_INC("ssat_swept_new_selections");
//      ait.del();
//      sweptSet.remove(v);
//    }
//  }
//
//  while(sweptAway.isNonEmpty()) {
//    SplitLevel v = sweptAway.pop();
//    if(sweptSet.find(v)) {
//      RSTAT_CTR_INC("ssat_swept_old_selections");
//      removedComps.push(v);
//    }
//  }
//
//
//}


//////////////
// SSplitter
//

SSplitter::SSplitter()
: _branchSelector(*this), _flushCounter(0)
{
  CALL("SSplitter::SSplitter");
}

SSplitter::~SSplitter()
{
  CALL("SSplitter::~SSplitter");

  while(_db.isNonEmpty()) {
    if(_db.top()) {
      delete _db.top();
    }
    _db.pop();
  }
}

void SSplitter::init(SaturationAlgorithm* sa)
{
  CALL("SSplitter::init");

  Splitter::init(sa);

  const Options& opts = getOptions();
  _branchSelector.init();
  _complBehavior = opts.ssplittingAddComplementary();
  _nonsplComps = opts.ssplittingNonsplittableComponents();

  _flushPeriod = opts.ssplittingFlushPeriod();
  _flushQuotient = opts.ssplittingFlushQuotient();
}

SplitLevel SSplitter::getNameFromLiteral(SATLiteral lit) const
{
  CALL("SSplitter::getNameFromLiteral");

  return (lit.var()-1)*2 + (lit.polarity() ? 0 : 1);
}
SATLiteral SSplitter::getLiteralFromName(SplitLevel compName) const
{
  unsigned var = compName/2 + 1;
  bool polarity = (compName&1)==0;
  return SATLiteral(var, polarity);
}
void SSplitter::collectDependenceLits(SplitSet* splits, SATLiteralStack& acc) const
{
  SplitSet::Iterator sit(*splits);
  while(sit.hasNext()) {
    SplitLevel nm = sit.next();
    acc.push(getLiteralFromName(nm).opposite());
  }
}

Clause* SSplitter::getComponentClause(SplitLevel name) const
{
  CALL("SSplitter::getComponentClause");
  ASS_L(name,_db.size());
  ASS_NEQ(_db[name],0);

  return _db[name]->component;
}


void SSplitter::addSATClause(SATClause* cl, bool branchRefutation)
{
  CALL("SSplitter::addSATClause");

  //TODO: push this kind of preprocessing into the SAT solver
  cl = Preprocess::removeDuplicateLiterals(cl);
  if(!cl) {
    return;
  }
  if(branchRefutation) {
    _haveBranchRefutation = true;
  }
  _clausesToBeAdded.push(cl);
}

void SSplitter::onAllProcessed()
{
  CALL("SSplitter::onAllProcessed");

  bool flushing = false;
  if(_flushPeriod) {
    _flushCounter++;
    if(_haveBranchRefutation) {
      _flushCounter = 0;
    }
    if(_flushCounter>=_flushPeriod && _clausesToBeAdded.isEmpty()) {
      flushing = true;
      _flushCounter = 0;
      _flushPeriod = static_cast<unsigned>(_flushPeriod*_flushQuotient);
    }
  }

  _haveBranchRefutation = false;

  if(_clausesToBeAdded.isEmpty() && !flushing) {
    return;
  }
  static SplitLevelStack toAdd;
  static SplitLevelStack toRemove;
  toAdd.reset();
  toRemove.reset();
  if(flushing) {
    LOG("sspl_flush","flushing");
    _branchSelector.flush(toAdd, toRemove);
  }
  else {
    _branchSelector.addSatClauses(_clausesToBeAdded, toAdd, toRemove);
    _clausesToBeAdded.reset();
  }

  if(toRemove.isNonEmpty()) {
    removeComponents(toRemove);
  }
  if(toAdd.isNonEmpty()) {
    addComponents(toAdd);
  }

  TRACE("sspl_sel_current_comps",
      unsigned bound = _db.size();
      tout << "currently selected components:" << endl;
      for(unsigned i=0; i<bound; ++i) {
	if(_db[i] && _db[i]->active) {
	  cout << i << "  --  " << (*_db[i]->component) << endl;
	}
      }
  );
}

bool SSplitter::handleNonSplittable(Clause* cl)
{
  CALL("SSplitter::handleNonSplittable");

  if(_nonsplComps==Options::SSNS_NONE) {
    return false;
  }
  SplitSet* sset = cl->splits();
  if(sset->size()==1 && _db[sset->sval()]->component==cl) {
    //the clause is already a component
    return false;
  }

  SplitLevel compName;
  Clause* compCl;
  if(!tryGetExistingComponentName(cl->length(), cl->literals(), compName, compCl)) {
    bool canCreate;
    switch(_nonsplComps) {
    case Options::SSNS_ALL:
      canCreate = true;
      break;
    case Options::SSNS_ALL_DEPENDENT:
      canCreate = !sset->isEmpty();
      break;
    case Options::SSNS_KNOWN:
      canCreate = false;
      break;
    default:
      ASSERTION_VIOLATION;
    }
    if(!canCreate) {
      return false;
    }
    RSTAT_CTR_INC("ssat_non_splittable_introduced_components");
    compName = getComponentName(cl->length(), cl->literals(), cl, compCl);
  }
  ASS_NEQ(cl,compCl);
  if(sset->member(compName)) {
    //we derived a component that depends on itself.
    //This derivation is therefore redundant, so we can skip it.
    RSTAT_CTR_INC("ssat_self_dependent_component");
    LOG_UNIT("sspl_ns_self_dependent",cl);
    return true;
  }

  static SATLiteralStack satLits;
  satLits.reset();
  collectDependenceLits(cl->splits(), satLits);
  satLits.push(getLiteralFromName(compName));

  SATClause* nsClause = SATClause::fromStack(satLits);
  ClauseList* namePremises = new ClauseList(compCl,0);
  nsClause->setInference(new FOSplittingInference(cl, namePremises));

  RSTAT_CTR_INC("ssat_non_splittable_sat_clauses");
  LOG("sspl_ns_sat_clauses","non-splittable "<<(*cl)<<" gave sat clause "<<(*nsClause));

  addSATClause(nsClause, false);
  return true;
}

/**
 * Attempt to split clause @b cl, and return true if successful
 */
bool SSplitter::doSplitting(Clause* cl)
{
  CALL("SSplitter::doSplitting");

  if(!splittingAllowed(cl)) {
    LOG_UNIT("sspl_nonsplits",cl);
    return false;
  }

  static Stack<CompRec> comps;
  comps.reset();
  if(!getComponents(cl, comps, false)) {
    LOG_UNIT("sspl_nonsplits",cl);
    return handleNonSplittable(cl);
  }

  static SATLiteralStack satClauseLits;
  satClauseLits.reset();

  collectDependenceLits(cl->splits(), satClauseLits);

  ClauseList* namePremises = 0;

  unsigned compCnt = comps.size();
  for(unsigned i=0; i<compCnt; ++i) {
    const CompRec& comp = comps[i];
    Clause* compCl;
    SplitLevel compName = getComponentName(comp, cl, compCl);
    SATLiteral nameLit = getLiteralFromName(compName);
    satClauseLits.push(nameLit);
    ClauseList::push(compCl, namePremises);
  }

  SATClause* splitClause = SATClause::fromStack(satClauseLits);
  splitClause->setInference(new FOSplittingInference(cl, namePremises));

  TRACE("sspl_splits",
      //we do the trace output before the call to addSATClause,
      //as there the list namePremises might be deleted
      tout << "splitting "<<(*cl)<<endl;
      tout << "  components:" << endl;
      ClauseList::Iterator nit(namePremises);
      while(nit.hasNext()) {
	tout << "    " << (*nit.next()) << endl;
      }
      tout << "final sat clause: " << (*splitClause) << endl;
  );

  addSATClause(splitClause, false);

  env.statistics->satSplits++;
  return true;
}

bool SSplitter::tryGetExistingComponentName(unsigned size, Literal* const * lits, SplitLevel& comp, Clause*& compCl)
{
  CALL("SSplitter::tryGetExistingComponentName");

  ClauseIterator existingComponents = _componentIdx.retrieveVariants(lits, size);

  if(!existingComponents.hasNext()) {
    return false;
  }
  compCl = existingComponents.next();
  ASS(!existingComponents.hasNext());
  comp = _compNames.get(compCl);
  return true;
}

Clause* SSplitter::buildAndInsertComponentClause(SplitLevel name, unsigned size, Literal* const * lits, Clause* orig)
{
  CALL("SSplitter::buildAndInsertComponentClause");
  ASS_EQ(_db[name],0);

  Unit::InputType inpType = orig ? orig->inputType() : Unit::AXIOM;
  Clause* compCl = Clause::fromIterator(getArrayishObjectIterator(lits, size), inpType, new Inference(Inference::SPLITTING_COMPONENT));

  _db[name] = new SplitRecord(compCl);

  compCl->setSplits(SplitSet::getSingleton(name));
  LOG_UNIT("sspl_comp_names", compCl);

  _componentIdx.insert(compCl);
  _compNames.insert(compCl, name);

  LOG_UNIT("sspl_comp_names", compCl);
  return compCl;
}

SplitLevel SSplitter::addNonGroundComponent(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl)
{
  CALL("SSplitter::addNonGroundComponent");
  ASS_REP(_db.size()%2==0, _db.size());
  ASS_G(size,0);
  ASS(forAll(getArrayishObjectIterator(lits, size), negPred(isGround))); //none of the literals can be ground

  SplitLevel compName = _db.size();
  _db.push(0);
  _db.push(0);
  _branchSelector.updateVarCnt();

  compCl = buildAndInsertComponentClause(compName, size, lits, orig);

  return compName;
}

SplitLevel SSplitter::addGroundComponent(Literal* lit, Clause* orig, Clause*& compCl)
{
  CALL("SSplitter::addGroundComponent");
  ASS_REP(_db.size()%2==0, _db.size());
  ASS(lit->ground());

  Literal* opposite = Literal::complementaryLiteral(lit);
  bool pos = lit->isPositive();

  SplitLevel compName;

  if(_complBehavior==Options::SSAC_NONE) {
    SplitLevel oppName;
    Clause* oppCl;
    if(tryGetExistingComponentName(1, &opposite, oppName, oppCl)) {
      ASS_EQ(oppName&1, opposite->isNegative());
      compName = oppName^1;
    }
    else {
      compName = _db.size() + (pos ? 0 : 1);
      _db.push(0);
      _db.push(0);
    }
  }
  else {
    //we insert both literal and its negation
    compName = _db.size() + (pos ? 0 : 1);
    unsigned oppName = compName^1;

    _db.push(0);
    _db.push(0);
    buildAndInsertComponentClause(oppName, 1, &opposite, orig);
  }
  compCl = buildAndInsertComponentClause(compName, 1, &lit, orig);

  _branchSelector.updateVarCnt();

  return compName;
}

/**
 * @param orig original clause used to determine input type of the component.
 *             Can be zero, in that case the input type is Unit::AXIOM
 */
SplitLevel SSplitter::getComponentName(const CompRec& comp, Clause* orig, Clause*& compCl)
{
  CALL("SSplitter::getComponentName/3");
  return getComponentName(comp.size(), comp.array(), orig, compCl);
}

/**
 * @param orig original clause used to determine input type of the component.
 *             Can be zero, in that case the input type is Unit::AXIOM
 */
SplitLevel SSplitter::getComponentName(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl)
{
  CALL("SSplitter::getComponentName/4");

  SplitLevel res;

  if(tryGetExistingComponentName(size, lits, res, compCl)) {
    RSTAT_CTR_INC("ssat_reused_components");
  }
  else {
    RSTAT_CTR_INC("ssat_new_components");

    if(size==1 && lits[0]->ground()) {
      res = addGroundComponent(lits[0], orig, compCl);
    }
    else {
      res = addNonGroundComponent(size, lits, orig, compCl);
    }
  }
  return res;
}

/**
 * Assign the @b SplitSet @b splits to the clause @b cl.
 */
void SSplitter::assignClauseSplitSet(Clause* cl, SplitSet* splits)
{
  CALL("SSplitter::assignClauseSplitSet");
  ASS(!cl->splits());

  cl->setSplits(splits);

  //update "children" field of relevant SplitRecords
  SplitSet::Iterator bsit(*splits);
  while(bsit.hasNext()) {
    SplitLevel slev=bsit.next();
    _db[slev]->children.push(cl);
  }
}

/**
 * Register the reduction of the @b cl clause
 */
void SSplitter::onClauseReduction(Clause* cl, ClauseIterator premises, Clause* replacement)
{
  CALL("SSplitter::onClauseReduction");
  ASS(cl);

  if(!premises.hasNext()) {
    ASS(!replacement || cl->splits()==replacement->splits());
    return;
  }

  LOG("sspl_reductions_prems","reduced clause: "<<(*cl));

  Clause* premise0 = premises.next();
  SplitSet* diff=premise0->splits();
  LOG("sspl_reductions_prems","reduction premise: "<<(*premise0));
  while(premises.hasNext()) {
    Clause* premise=premises.next();
    LOG("sspl_reductions_prems","reduction premise: "<<(*premise));
    ASS(premise);
    diff=diff->getUnion(premise->splits());
  }
  if(replacement) {
    LOG("sspl_reductions_prems","reduction replacement: "<<(*replacement));
    diff=diff->getUnion(replacement->splits());
  }
  diff=diff->subtract(cl->splits());
  
  LOG("sspl_reductions","Reduced "<<(*cl)<<". Added to reduced stack on levels {"<<diff->toString()<<"}.");

#if VDEBUG
  assertSplitLevelsActive(diff);
#endif

  if(diff->isEmpty()) {
    return;
  }

  cl->incReductionTimestamp();
  //BDDs are disabled when we do ssplitting so they can only contain false
  ASS_REP(BDD::instance()->isFalse(cl->prop()), BDD::instance()->toString(cl->prop()));
  SplitSet::Iterator dit(*diff);
  while(dit.hasNext()) {
    SplitLevel slev=dit.next();
    _db[slev]->addReduced(cl);
  }
}

void SSplitter::assertSplitLevelsActive(SplitSet* s)
{
  CALL("SSplitter::assertSplitLevelsActive");

  SplitSet::Iterator sit(*s);
  while(sit.hasNext()) {
    SplitLevel lev=sit.next();
    ASS_REP(lev<_db.size(), lev);
    ASS_REP(_db[lev]!=0, lev);
    ASS_REP(_db[lev]->active, lev);
  }
}

void SSplitter::onNewClause(Clause* cl)
{
  CALL("SSplitter::onNewClause");

  if(!cl->splits()) {
    SplitSet* splits=getNewClauseSplitSet(cl);
    assignClauseSplitSet(cl, splits);
    LOG("sspl_new_cl_levels","New clause assigned levels: "<<(*cl));
  }

#if VDEBUG
  assertSplitLevelsActive(cl->splits());
#endif
}

/**
 * Return a split set of a new clause
 *
 * Assumes that clauses referred to by cl->inference() object
 * are actual premisses of @b cl. (This holds when BDDs are not
 * used.)
 */
SplitSet* SSplitter::getNewClauseSplitSet(Clause* cl)
{
  CALL("SSplitter::getNewClauseSplitSet");

  SplitSet* res;
  Inference* inf=cl->inference();
  Inference::Iterator it=inf->iterator();

  res=SplitSet::getEmpty();

  while(inf->hasNext(it)) {
    Unit* premu=inf->next(it);
    if(!premu->isClause()) {
      //the premise comes from preprocessing
      continue;
    }
    Clause* prem=static_cast<Clause*>(premu);
    if(!prem->splits()) {
      //the premise comes from preprocessing
      continue;
    }

    res=res->getUnion(prem->splits());
  }
  return res;
}


SSplitter::SplitRecord::~SplitRecord()
{
  CALL("SSplitter::SplitRecord::~SplitRecord");
  component->decRefCnt();
  while(reduced.isNonEmpty()) {
    Clause* cl = reduced.pop().clause;
    cl->decRefCnt();
  }
}

/**
 * Add a reduced clause to the @b SplitRecord object.
 */
void SSplitter::SplitRecord::addReduced(Clause* cl)
{
  CALL("SSplitter::SplitRecord::addReduced");

  cl->incRefCnt(); //dec when popped from the '_db[slev]->reduced' stack in backtrack method
  reduced.push(ReductionRecord(cl->getReductionTimestamp(),cl));
}

bool SSplitter::handleEmptyClause(Clause* cl)
{
  CALL("SSplitter::handleEmptyClause");

  if(cl->splits()->isEmpty()) {
    return false;
  }
  ASS(BDD::instance()->isFalse(cl->prop()));

  static SATLiteralStack conflictLits;
  conflictLits.reset();

  collectDependenceLits(cl->splits(), conflictLits);
  SATClause* confl = SATClause::fromStack(conflictLits);
  confl->setInference(new FOConversionInference(cl));

  LOG("sspl_confl","FO contradiction "<<(*cl)<<" gave SAT conflict clause "<<(*confl));
  TRACE("sspl_confl_derivations",
      tout << "conflict derivation:" << endl;
      Refutation(cl, false).output(tout);
  );
  RSTAT_MCTR_INC("sspl_confl_len", confl->length());

  addSATClause(confl, true);

  env.statistics->satSplitRefutations++;
  return true;
}


void SSplitter::addComponents(const SplitLevelStack& toAdd)
{
  CALL("SSplitter::addComponents");

  SplitLevelStack::ConstIterator slit(toAdd);
  while(slit.hasNext()) {
    SplitLevel sl = slit.next();
    SplitRecord* sr = _db[sl];
    ASS(sr);
    ASS(!sr->active);
    sr->active = true;
    //simplifications may set prop part to true, but when we add the
    //clause, we cannot assume is it still simplified
    sr->component->setProp(BDD::instance()->getFalse());

    ASS(sr->children.isEmpty());
    //we need to put the component among children, so that it is backtracked
    //when we remove the component
    sr->children.push(sr->component);

    _sa->addNewClause(sr->component);
  }
}

/**
 * Perform backtracking of split levels in @c toRemove.
 *
 * Can be called only when there are no unprocessed clauses left.
 * This is to allow for easy clause removal from the saturation algorithm.
 */
void SSplitter::removeComponents(const SplitLevelStack& toRemove)
{
  CALL("SSplitter::backtrack");
  ASS(_sa->clausesFlushed());

  Clause::requestAux();
  static RCClauseStack trashed;
  static RCClauseStack restored;
  ASS(restored.isEmpty());
  ASS(trashed.isEmpty());

  SplitSet* backtracked = SplitSet::getFromArray(toRemove.begin(), toRemove.size());

  LOG("sspl_rm","removal of splitting levels " << backtracked);

  SplitSet::Iterator blit(*backtracked);
  while(blit.hasNext()) {
    SplitLevel bl=blit.next();
    SplitRecord* sr=_db[bl];
    ASS(sr);

    while(sr->children.isNonEmpty()) {
      Clause* ccl=sr->children.popWithoutDec();
      if(!ccl->hasAux()) {
	ASS(ccl->splits()->member(bl));
	LOG_UNIT("sspl_rm_backtracked", ccl);
	if(ccl->store()!=Clause::NONE) {
	  _sa->removeActiveOrPassiveClause(ccl);
	  ASS_EQ(ccl->store(), Clause::NONE);
	}
	ccl->setAux(0);
	ccl->incReductionTimestamp();
      }
      ccl->decRefCnt(); //decrease corresponding to sr->children.popWithoutDec()
    }
  }

  SplitSet::Iterator blit2(*backtracked);
  while(blit2.hasNext()) {
    SplitLevel bl=blit2.next();
    SplitRecord* sr=_db[bl];

    while(sr->reduced.isNonEmpty()) {
      ReductionRecord rrec=sr->reduced.pop();
      Clause* rcl=rrec.clause;
      if(rrec.timestamp==rcl->getReductionTimestamp()) {
	restored.push(rcl);
      }
      rcl->decRefCnt(); //inc when pushed on the 'sr->reduced' stack in SSplitter::SplitRecord::addReduced
    }

    ASS(sr->active);
    sr->active = false;
  }

  while(restored.isNonEmpty()) {
    Clause* rcl=restored.popWithoutDec();
    if(!rcl->hasAux()) {
      ASS(!rcl->splits()->hasIntersection(backtracked));
      rcl->setAux(0);
      ASS_EQ(rcl->store(), Clause::NONE);
      rcl->incReductionTimestamp();
      rcl->setProp(BDD::instance()->getFalse()); //we asserted it was false in onClauseReduction
      _sa->addNewClause(rcl);
  #if VDEBUG
      //check that restored clause does not depend on inactive splits
      assertSplitLevelsActive(rcl->splits());
  #endif
      LOG_UNIT("sspl_rm_restored", rcl);
    }
    rcl->decRefCnt(); //belongs to restored.popWithoutDec();
  }

  Clause::releaseAux();
}

}
