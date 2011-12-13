/**
 * @file SSplitter.cpp
 * Implements class SSplitter.
 */

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RCClauseStack.hpp"
#include "Kernel/TermIterators.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "SAT/Preprocess.hpp"
#include "SAT/SATInference.hpp"
#include "SAT/TWLSolver.hpp"

#include "SSplitter.hpp"
#include "SaturationAlgorithm.hpp"

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

  _solver = new TWLSolver(_parent.getOptions(), true);
}

void SSplittingBranchSelector::ensureVarCnt(unsigned varCnt)
{
  CALL("SSplittingBranchSelector::ensureVarCnt");

  LOG("sspl_var_cnt","ensuring varCnt to "<<varCnt);
  _solver->ensureVarCnt(varCnt);
  _selected.expand(varCnt);
  _watcher.expand(varCnt);
}

bool SSplittingBranchSelector::hasPositiveLiteral(SATClause* cl)
{
  CALL("SSplittingBranchSelector::hasPositiveLiteral");

  SATClause::Iterator it(*cl);
  while(it.hasNext()) {
    SATLiteral l = it.next();
    if(l.isPositive()) { return true; }
  }
  return false;
}

void SSplittingBranchSelector::handleSatRefutation(SATClause* ref)
{
  CALL("SSplittingBranchSelector::handleSatRefutation");

  UnitList* prems = SATInference::getFOPremises(ref);
  Inference* foInf = new InferenceMany(Inference::SPLITTING, prems);
  Clause* foRef = Clause::fromIterator(LiteralIterator::getEmpty(), Unit::CONJECTURE, foInf);
  throw MainLoop::RefutationFoundException(foRef);
}

void SSplittingBranchSelector::addSatClauses(const SATClauseStack& clauses,
    SplitLevelStack& addedComps, SplitLevelStack& removedComps)
{
  CALL("SSplittingBranchSelector::addSatClauses");
  ASS(addedComps.isEmpty());
  ASS(removedComps.isEmpty());

  _unprocessed.loadFromIterator(
      getFilteredIterator(SATClauseStack::ConstIterator(clauses), hasPositiveLiteral) );

  _solver->addClauses(pvi( SATClauseStack::ConstIterator(clauses) ), false);

  if(_solver->getStatus()==SATSolver::UNSATISFIABLE) {
    LOG("sspl_sel","cannot fix selection, refutation found");
    SATClause* satRefutation = _solver->getRefutation();
    handleSatRefutation(satRefutation);
  }
  ASS_EQ(_solver->getStatus(),SATSolver::SATISFIABLE);

  deselectByModel(removedComps);
  fixUnprocessed(addedComps);

  COND_LOG("sspl_sel",addedComps.isNonEmpty()&&removedComps.isNonEmpty(), "selection changed by addition of SAT clauses");
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

void SSplittingBranchSelector::select(SplitLevel var)
{
  CALL("SSplittingBranchSelector::select");
  ASS(!_selected.find(var));
  ASS(_solver->getAssignment(var)!=false);

  _selected.insert(var);
  SATClauseStack& watched = _watcher[var];
  _unprocessed.loadFromIterator(SATClauseStack::Iterator(watched));
  watched.reset();
}

void SSplittingBranchSelector::deselectByModel(SplitLevelStack& removedComps)
{
  CALL("SSplittingBranchSelector::deselectByModel");

  static SplitLevelStack toDeselect;
  toDeselect.reset();

  ArraySet::Iterator sit(_selected);
  while(sit.hasNext()) {
    unsigned sel = sit.next();
    if(_solver->getAssignment(sel)==false) {
      toDeselect.push(sel);
    }
  }

  while(toDeselect.isNonEmpty()) {
    unsigned sel = toDeselect.pop();
    removedComps.push(sel);
    _selected.remove(sel);
    SATClauseStack& watched = _watcher[sel];
    _unprocessed.loadFromIterator(SATClauseStack::Iterator(watched));
    watched.reset();
  }
}

void SSplittingBranchSelector::fixUnprocessed(SplitLevelStack& addedComps)
{
  CALL("SSplittingBranchSelector::fixUnprocessed");

  while(_unprocessed.isNonEmpty()) {
    SATClause* cl = _unprocessed.pop();
    if(tryAddingToWatch(cl)) { continue; }
    SplitLevel toSelect = getVarToSelect(cl);
    addedComps.push(toSelect);
    select(toSelect);
    _watcher[toSelect].push(cl);
  }
}

bool SSplittingBranchSelector::tryAddingToWatch(SATClause* cl)
{
  CALL("SSplittingBranchSelector::tryAddingToWatch");

  //TODO: pick smartly watch to add to
  SATClause::Iterator it(*cl);
  while(it.hasNext()) {
    SATLiteral lit = it.next();
    SplitLevel var = lit.var();
    bool isSel = _selected.find(var);
    if(lit.polarity()==isSel) {
      _watcher[var].push(cl);
      return true;
    }
  }
  return false;
}

SplitLevel SSplittingBranchSelector::getVarToSelect(SATClause* cl)
{
  CALL("SSplittingBranchSelector::getVarToSelect");

  //TODO: pick smartly literal to select
  SATClause::Iterator it(*cl);
  while(it.hasNext()) {
    SATLiteral lit = it.next();
    SplitLevel var = lit.var();
    if(!lit.polarity()) {
      //clause should be unsatisfied, therefore negative literals must be selected
      ASS(_selected.find(var));
      continue;
    }
    ASS(!_selected.find(var)); //clause should be unsatisfied
    if(_solver->getAssignment(var)==false) { continue; }

    return lit.var();
  }
  ASSERTION_VIOLATION;
}

//////////////
// SSplitter
//

SSplitter::SSplitter()
: _branchSelector(*this)
{
  CALL("SSplitter::SSplitter");

  //puth 0 at the 0-th position as we don't use component name 0
  _db.push(0);
}

SSplitter::~SSplitter()
{
  CALL("SSplitter::~SSplitter");

  while(_db.isNonEmpty()) {
    ASS_EQ(_db.top()!=0, _db.size()>1);
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
  _branchSelector.init();
  _addGroundNegation=getOptions().splitAddGroundNegation();
}


SATLiteral SSplitter::getLiteralFromName(SplitLevel compName)
{
  return SATLiteral(compName, true);
}
void SSplitter::collectDependenceLits(SplitSet* splits, SATLiteralStack& acc)
{
  SplitSet::Iterator sit(*splits);
  while(sit.hasNext()) {
    SplitLevel nm = sit.next();
    acc.push(SATLiteral(nm, false));
  }
}

SplitLevel SSplitter::getNewComponentName(Clause* comp)
{
  CALL("SSplitter::getNewComponentName");

  unsigned res = _db.size();
  _db.push(new SplitRecord(comp));
  _branchSelector.ensureVarCnt(res+1);

  return res;
}

Clause* SSplitter::getComponentClause(SplitLevel name)
{
  CALL("SSplitter::getComponentClause");
  ASS_L(name,_db.size());
  ASS_NEQ(_db[name],0);

  return _db[name]->component;
}


void SSplitter::addSATClause(SATClause* cl)
{
  CALL("SSplitter::addSATClause");

  //TODO: push this kind of preprocessing into the SAT solver
  cl = Preprocess::removeDuplicateLiterals(cl);
  if(!cl) {
    return;
  }
  _clausesToBeAdded.push(cl);
}

void SSplitter::onAllProcessed()
{
  CALL("SSplitter::onAllProcessed");

  if(_clausesToBeAdded.isEmpty()) {
    return;
  }
  static SplitLevelStack toAdd;
  static SplitLevelStack toRemove;
  toAdd.reset();
  toRemove.reset();
  _branchSelector.addSatClauses(_clausesToBeAdded, toAdd, toRemove);
  _clausesToBeAdded.reset();

  if(toRemove.isNonEmpty()) {
    removeComponents(toRemove);
  }
  if(toAdd.isNonEmpty()) {
    addComponents(toAdd);
  }

  TRACE("sspl_sel_current_comps",
      unsigned bound = _db.size();
      tout << "currently selected components:" << endl;
      for(unsigned i=1; i<bound; ++i) {
	if(_db[i]->active) {
	  cout << i << "  --  " << (*_db[i]->component) << endl;
	}
      }
  );
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
    return false;
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

  addSATClause(splitClause);

  env.statistics->satSplits++;
  return true;
}

SplitLevel SSplitter::getComponentName(const CompRec& comp, Clause* orig, Clause*& compCl)
{
  CALL("SSplitter::getComponentName");

  ClauseIterator existingComponents = _componentIdx.retrieveVariants(comp.array(), comp.size());

  if(existingComponents.hasNext()) {
    compCl = existingComponents.next();
    ASS(!existingComponents.hasNext());
    return _compNames.get(compCl);
  }
  else {
    compCl = Clause::fromIterator(CompRec::Iterator(comp), orig->inputType(), new Inference(Inference::SPLITTING_COMPONENT));
    SplitLevel compName = getNewComponentName(compCl);
    assignClauseSplitSet(compCl, SplitSet::getSingleton(compName));
    LOG_UNIT("sspl_comp_names", compCl);

    _componentIdx.insert(compCl);
    _compNames.insert(compCl, compName);

    return compName;
  }
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

  SplitSet* diff=premises.next()->splits();
  while(premises.hasNext()) {
    Clause* premise=premises.next();
    ASS(premise);
    diff=diff->getUnion(premise->splits());
  }
  if(replacement) {
    diff=diff->getUnion(replacement->splits());
  }
  diff=diff->subtract(cl->splits());
  
#if VDEBUG
  assertSplitLevelsActive(diff);
#endif

  LOG("sspl_reductions","Reduced "<<(*cl)<<". Added to reduced stack on levels {"<<diff->toString()<<"}.");

  if(diff->isEmpty()) {
    return;
  }

  cl->incReductionTimestamp();
  //BDDs are disabled when we do backtracking splitting so they can only contain false
  ASS(BDD::instance()->isFalse(cl->prop()));
  SplitSet::Iterator dit(*diff);
  while(dit.hasNext()) {
    SplitLevel slev=dit.next();
    _db[slev]->addReduced(cl);
  }
}

void SSplitter::assertSplitLevelsActive(SplitSet* s)
{
  CALL("SSplitter::assertSplitLevelsExist");

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

  addSATClause(confl);

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
    ASS(!sr->active);
    sr->active = true;
    //simplifications may set prop part to true, but when we add the
    //clause, we cannot assume is it still simplified
    sr->component->setProp(BDD::instance()->getFalse());
    _sa->addNewClause(sr->component);
  }
}

/**
 * Perform backtracking allowed for by empty clauses in @b emptyClauses
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

    while(sr->children.isNonEmpty()) {
      Clause* ccl=sr->children.popWithoutDec();
      if(!ccl->hasAux()) {
	ASS(ccl->splits()->member(bl));
	if(ccl->store()!=Clause::BACKTRACKED) {
	  trashed.push(ccl);
	}
	ccl->setAux(0);
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

  while(trashed.isNonEmpty()) {
    Clause* tcl=trashed.popWithoutDec();
    LOG_UNIT("sspl_rm_backtracked", tcl);
    if(tcl->store()!=Clause::NONE) {
      _sa->removeActiveOrPassiveClause(tcl);
      ASS_EQ(tcl->store(), Clause::NONE);
    }
    tcl->setStore(Clause::BACKTRACKED);
    tcl->decRefCnt(); //belongs to trashed.popWithoutDec()
  }

  while(restored.isNonEmpty()) {
    Clause* rcl=restored.popWithoutDec();
    if(!rcl->hasAux() && rcl->store()!=Clause::BACKTRACKED) {
      ASS(!rcl->splits()->hasIntersection(backtracked));
      rcl->setAux(0);
      ASS_EQ(rcl->store(), Clause::NONE);
      rcl->incReductionTimestamp();
      rcl->setProp(BDD::instance()->getFalse()); //we asserted it was false in onClauseReduction
      _sa->addNewClause(rcl);
  #if VDEBUG
      //check that restored clause does not depend on splits that were already backtracked
      assertSplitLevelsActive(rcl->splits());
  #endif
      LOG_UNIT("sspl_rm_restored", rcl);
    }
    rcl->decRefCnt(); //belongs to restored.popWithoutDec();
  }

  Clause::releaseAux();
}

}
