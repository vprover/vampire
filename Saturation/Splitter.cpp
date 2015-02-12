/**
 * @file Splitter.cpp
 * Implements class Splitter.
 */

#include "Splitter.hpp"

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Signature.hpp"
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
#include "SAT/LingelingInterfacing.hpp"
#include "SAT/MinimizingSolver.hpp"
#include "SAT/BufferedSolver.hpp"
#include "SAT/MinisatInterfacing.hpp"

#include "DP/ShortConflictMetaDP.hpp"

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
// SplittingBranchSelector
//

void SplittingBranchSelector::init()
{
  CALL("SplittingBranchSelector::init");

  _eagerRemoval = _parent.getOptions().splittingEagerRemoval();
  _handleZeroImplied = _parent.getOptions().splittingHandleZeroImplied();
  _literalPolarityAdvice = _parent.getOptions().splittingLiteralPolarityAdvice();

  switch(_parent.getOptions().satSolver()){
    case Options::SatSolver::BUFFERED_VAMPIRE:
      _solver = new BufferedSolver(new TWLSolver(_parent.getOptions(),true));
      break;
    case Options::SatSolver::VAMPIRE:  
      _solver = new TWLSolver(_parent.getOptions(), true);
      break;
    case Options::SatSolver::BUFFERED_LINGELING: 
      _solver = new BufferedSolver(new LingelingInterfacing(_parent.getOptions(), true));
      break;
    case Options::SatSolver::LINGELING: 
      _solver = new LingelingInterfacing(_parent.getOptions(), true);
      break;
    case Options::SatSolver::BUFFERED_MINISAT:
      _solver = new BufferedSolver(new MinisatInterfacing(_parent.getOptions(),true));
      break;
    case Options::SatSolver::MINISAT:
      _solver = new MinisatInterfacing(_parent.getOptions(),true);
      break;      
    default:
      ASSERTION_VIOLATION_REP(_parent.getOptions().satSolver());
  }

  switch(_parent.getOptions().splittingMinimizeModel()){
    case Options::SplittingMinimizeModel::OFF:
      // Do nothing - we don't want to minimise the model
      break;
    case Options::SplittingMinimizeModel::ALL:
    case Options::SplittingMinimizeModel::SCO:
      _solver = new MinimizingSolver(_solver.release());
      break;
    default:
      ASSERTION_VIOLATION_REP(_parent.getOptions().splittingMinimizeModel());
  }
  _minSCO = _parent.getOptions().splittingMinimizeModel() == Options::SplittingMinimizeModel::SCO;


#if DEBUG_MIN_SOLVER
  _solver = new Test::CheckedSatSolver(_solver.release());
#endif


  if(_parent.getOptions().splittingCongruenceClosure() != Options::SplittingCongruenceClosure::OFF) {
    _dp = new DP::SimpleCongruenceClosure(_parent.getOrdering());
    if (_parent.getOptions().ccUnsatCores() == Options::CCUnsatCores::SMALL_ONES) {
      _dp = new ShortConflictMetaDP(_dp.release(), _parent.satNaming(), *_solver);
    }
    _ccMultipleCores = (_parent.getOptions().ccUnsatCores() != Options::CCUnsatCores::FIRST);

    _ccModel = (_parent.getOptions().splittingCongruenceClosure() == Options::SplittingCongruenceClosure::MODEL);
    if (_ccModel) {
      _dpModel = new DP::SimpleCongruenceClosure(_parent.getOrdering());
    }
  }
}

void SplittingBranchSelector::updateVarCnt()
{
  CALL("SplittingBranchSelector::ensureVarCnt");

  unsigned satVarCnt = _parent.maxSatVar()+1;
  unsigned splitLvlCnt = _parent.splitLevelCnt();

  _solver->ensureVarCnt(satVarCnt);
  _selected.expand(splitLvlCnt);
  _trueInCCModel.expand(satVarCnt);
  _zeroImplieds.expand(satVarCnt,false);
}

/**
 * The solver should consider making @b lit false by default.
 */
void SplittingBranchSelector::considerPolarityAdvice(SATLiteral lit)
{
  CALL("SplittingBranchSelector::considerPolarityAdvice");

  switch (_literalPolarityAdvice) {
    case Options::SplittingLiteralPolarityAdvice::FORCE_FALSE:
      _solver->forcePolarity(lit.var(),lit.oppositePolarity());
      break;
    case Options::SplittingLiteralPolarityAdvice::FORCE_RND:      
      _solver->forcePolarity(lit.var(),Random::getBit());
      break;
    case Options::SplittingLiteralPolarityAdvice::NONE:
      // do nothing
      break;
    case Options::SplittingLiteralPolarityAdvice::SUGGEST_FALSE:
      _solver->suggestPolarity(lit.var(),lit.oppositePolarity());
      break;
    case Options::SplittingLiteralPolarityAdvice::SUGGEST_RND:
      _solver->suggestPolarity(lit.var(),Random::getBit());
      break;
  }
}

void SplittingBranchSelector::handleSatRefutation(SATClause* ref)
{
  CALL("SplittingBranchSelector::handleSatRefutation");

  UnitList* prems = SATInference::getFOPremises(ref);
  Inference* foInf = new InferenceMany(Inference::SAT_SPLITTING_REFUTATION, prems);
  Clause* foRef = Clause::fromIterator(LiteralIterator::getEmpty(), Unit::CONJECTURE, foInf);
  throw MainLoop::RefutationFoundException(foRef);
}

SATSolver::VarAssignment SplittingBranchSelector::getSolverAssimentConsideringCCModel(unsigned var) {
  CALL("SplittingBranchSelector::getSolverAssimentConsideringCCModel");

  SATSolver::VarAssignment asgn = _solver->getAssignment(var);

  if (!_ccModel || asgn == SATSolver::FALSE) {
    return asgn;
  }

  // if we work with ccModel, the cc-model overrides the satsolver, but only for positive ground equalities

  SAT2FO& s2f = _parent.satNaming();

  Literal* lit = s2f.toFO(SATLiteral(var,true));

  if (lit && lit->isEquality() && lit->ground()) {
    return _trueInCCModel.find(var) ? SATSolver::TRUE : SATSolver::DONT_CARE;
  } else {
    return asgn;
  }
}

static const int AGE_NOT_FILLED = -1;

int SplittingBranchSelector::assertedGroundPositiveEqualityCompomentMaxAge()
{
  CALL("SplittingBranchSelector::assertedGroundPositiveEqualityCompomentMaxAge");

  int max = 0;

  unsigned maxSatVar = _parent.maxSatVar();
  for(unsigned i=1; i<=maxSatVar; i++) {
    SATSolver::VarAssignment asgn = _solver->getAssignment(i);
    if(asgn==SATSolver::DONT_CARE) {
      continue;
    }
    SATLiteral sl(i, asgn==SATSolver::TRUE);
    SplitLevel name = _parent.getNameFromLiteral(sl);
    if (!_parent.isUsedName(name)) {
      continue;
    }
    Clause* compCl = _parent.getComponentClause(name);
    if (compCl->length() != 1) {
      continue;
    }
    Literal* l = (*compCl)[0];
    if (l->ground() && l->isEquality() && l->isPositive()) {
      int clAge = compCl->age();

      if (clAge > max) {
        max = clAge;
      }
    }
  }

  return max;
}

SATSolver::Status SplittingBranchSelector::processDPConflicts()
{
  CALL("SplittingBranchSelector::processDPConflicts");
  // ASS(_solver->getStatus()==SATSolver::SATISFIABLE);

  if(!_dp) {
    return SATSolver::SATISFIABLE;
  }
  
  SAT2FO& s2f = _parent.satNaming();
  static LiteralStack gndAssignment;
  static LiteralStack unsatCore;

  static SATClauseStack conflictClauses;

  while (true) { // breaks inside
    {
      TimeCounter tc(TC_CONGRUENCE_CLOSURE);
    
      gndAssignment.reset();
      // collects only ground literals, because it known only about them ...
      s2f.collectAssignment(*_solver, gndAssignment); 
      // ... moreover, _dp->addLiterals will filter the set anyway

      _dp->reset();
      _dp->addLiterals(pvi( LiteralStack::ConstIterator(gndAssignment) ));
      DecisionProcedure::Status dpStatus = _dp->getStatus(_ccMultipleCores);

      if(dpStatus!=DecisionProcedure::UNSATISFIABLE) {
        break;
      }

      conflictClauses.reset();
      unsigned unsatCoreCnt = _dp->getUnsatCoreCount();
      for(unsigned i=0; i<unsatCoreCnt; i++) {
        unsatCore.reset();
        _dp->getUnsatCore(unsatCore, i);
        SATClause* conflCl = s2f.createConflictClause(unsatCore);
        conflictClauses.push(conflCl);
      }
    }

    RSTAT_CTR_INC("ssat_dp_conflict");
    RSTAT_CTR_INC_MANY("ssat_dp_conflict_clauses",conflictClauses.size());    
    
    {
    	TimeCounter tca(TC_SAT_SOLVER);
      if (_minSCO) {
        _solver->addClausesIgnoredInPartialModel(pvi( SATClauseStack::Iterator(conflictClauses)));
      } else {
        _solver->addClauses(pvi( SATClauseStack::Iterator(conflictClauses)));
      }
    	
      if (_solver->solve() == SATSolver::UNSATISFIABLE) {
        return SATSolver::UNSATISFIABLE;
      }
    }
  }
  
  // ASS(_solver->getStatus()==SATSolver::SATISFIABLE);
  if (_ccModel) {
    TimeCounter tc(TC_CCMODEL);

    static LiteralStack model;
    model.reset();

    _dpModel->reset();
    _dpModel->addLiterals(pvi( LiteralStack::ConstIterator(gndAssignment) ),true /*only equalities now*/);
    ALWAYS(_dpModel->getStatus(false) == DecisionProcedure::SATISFIABLE);
    _dpModel->getModel(model);

    _trueInCCModel.reset();

    // cout << "Obtained a model " << endl;
    LiteralStack::Iterator it(model);
    while(it.hasNext()) {
      Literal* lit = it.next();

      // cout << lit->toString() << endl;

      ASS(lit->isPositive());
      ASS(lit->isEquality());
      ASS(lit->ground());

      Clause* compCl;
      SplitLevel level = _parent.tryGetComponentNameOrAddNew(1,&lit,0,compCl);
      if (compCl->age() == AGE_NOT_FILLED) { // added new
        int parentMaxAge = assertedGroundPositiveEqualityCompomentMaxAge();
        // This is the max of all the positive ground units that went into the DP.
        // As such, is overestimates that "true age" that could be computed
        // as the max over the true parents of this equality
        // (we are lazy and cannot know the true parents without effort).
        compCl->setAge(parentMaxAge);
      }

      SATLiteral slit = _parent.getLiteralFromName(level);
      ASS(slit.polarity());
      _trueInCCModel.insert(slit.var());
    }
  }
  
  return SATSolver::SATISFIABLE;
}

void SplittingBranchSelector::updateSelection(unsigned satVar, SATSolver::VarAssignment asgn,
    SplitLevelStack& addedComps, SplitLevelStack& removedComps)
{
  CALL("SplittingBranchSelector::updateSelection");
  ASS_NEQ(asgn, SATSolver::NOT_KNOWN); //we always do full SAT solving, so there shouldn't be unknown variables

  SplitLevel posLvl = _parent.getNameFromLiteral(SATLiteral(satVar, true));
  SplitLevel negLvl = _parent.getNameFromLiteral(SATLiteral(satVar, false));

  switch(asgn) {
  case SATSolver::TRUE: 
    if(!_selected.find(posLvl) && _parent.isUsedName(posLvl)) {
      _selected.insert(posLvl);
      addedComps.push(posLvl);
    }
    if(_selected.find(negLvl)) {
      _selected.remove(negLvl);
      removedComps.push(negLvl);
    }
    break;
  case SATSolver::FALSE:    
    if(!_selected.find(negLvl) && _parent.isUsedName(negLvl)) {
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
    } else {
      if(_ccModel && _selected.find(negLvl) && (_solver->getAssignment(satVar) == SATSolver::TRUE)) {
        // The minimized model from the SATSolver says that a removal should happen for the negative equality.
        // At the same ccModel has a better way of expressing the (positive version of the) equality and so said don't-care instead.
        // But we must remove the negative equality now (even though we are lazy about removals in general here)
#ifdef VDEBUG
        {
          Clause* cc = _parent.getComponentClause(negLvl);
          ASS(cc && cc->size() == 1);
          Literal* l = (*cc)[0];
          ASS(l->ground() && l->isEquality() && l->isNegative());
        }
#endif

        _selected.remove(negLvl);
        removedComps.push(negLvl);
      }
    }
    break;
  default:
    ASSERTION_VIOLATION;
  }

}

void SplittingBranchSelector::addSatClauses(
        const SATClauseStack& regularClauses,
        const SATClauseStack& conflictClauses,
    SplitLevelStack& addedComps, SplitLevelStack& removedComps)
{
  CALL("SplittingBranchSelector::addSatClauses");
  ASS(addedComps.isEmpty());
  ASS(removedComps.isEmpty());

  RSTAT_CTR_INC_MANY("ssat_sat_clauses",regularClauses.size()+conflictClauses.size());  
  
  _solver->addClauses(pvi( SATClauseStack::ConstIterator(regularClauses) ));
  if (_minSCO) {
    _solver->addClausesIgnoredInPartialModel(pvi( SATClauseStack::ConstIterator(conflictClauses) ));
  } else {
    _solver->addClauses(pvi( SATClauseStack::ConstIterator(conflictClauses) ));
  }
  
  SATSolver::Status stat;
  {
    TimeCounter tc1(TC_SAT_SOLVER);
    stat = _solver->solve();
  }
  if (stat != SATSolver::UNSATISFIABLE) {
    stat = processDPConflicts();
  }
  if(stat == SATSolver::UNSATISFIABLE) {
    SATClause* satRefutation = _solver->getRefutation();
    handleSatRefutation(satRefutation); // noreturn!
  }
  ASS_EQ(stat,SATSolver::SATISFIABLE);

  TimeCounter tc(TC_SPLITTING_COMPONENT_SELECTION);

  unsigned maxSatVar = _parent.maxSatVar();
  unsigned _usedcnt=0; // for the statistics below
  for(unsigned i=1; i<=maxSatVar; i++) {
    SATSolver::VarAssignment asgn = getSolverAssimentConsideringCCModel(i);
    updateSelection(i, asgn, addedComps, removedComps);
    
    if (asgn != SATSolver::DONT_CARE) {
      _usedcnt++;
    }
  }
  if(maxSatVar>=1){
    int percent = (_usedcnt *100) / maxSatVar;
    RSTAT_MCTR_INC("minimise_model_percent",percent);
  }
  
  RSTAT_CTR_INC_MANY("ssat_usual_activations", addedComps.size());
  RSTAT_CTR_INC_MANY("ssat_usual_deactivations", removedComps.size());
}

/**
 * Switch to a (randomly) different splitting branch.
 */
void SplittingBranchSelector::flush(SplitLevelStack& addedComps, SplitLevelStack& removedComps)
{
  CALL("SplittingBranchSelector::flush");
  ASS(addedComps.isEmpty());
  ASS(removedComps.isEmpty());
  
  // if(_solver->getStatus()==SATSolver::UNKNOWN) 
  {    
  	TimeCounter tca(TC_SAT_SOLVER);
    // TODO: this may be here just to make sure that the solver's internal status
    // in not UNKNOWN, which would violate assertion in randomizeAssignment
    _solver->solve();
  }
  // ASS_EQ(_solver->getStatus(), SATSolver::SATISFIABLE); 
  _solver->randomizeAssignment();

  if(processDPConflicts() == SATSolver::UNSATISFIABLE) {
    SATClause* satRefutation = _solver->getRefutation();
    handleSatRefutation(satRefutation); // noreturn!
  }
  // ASS_EQ(_solver->getStatus(), SATSolver::SATISFIABLE); 

  unsigned maxSatVar = _parent.maxSatVar();
  unsigned _usedcnt=0; // for the statistics below
  for(unsigned i=1; i<=maxSatVar; i++) {
    SATSolver::VarAssignment asgn = getSolverAssimentConsideringCCModel(i);
    updateSelection(i, asgn, addedComps, removedComps);
    
    if (asgn != SATSolver::DONT_CARE) {
      _usedcnt++;
    }
  }
  if(maxSatVar>=1){
    int percent = (_usedcnt *100) / maxSatVar;
    RSTAT_MCTR_INC("minimise_model_percent",percent);
  }

  RSTAT_CTR_INC_MANY("ssat_added_by_flush",addedComps.size());
  RSTAT_CTR_INC_MANY("ssat_removed_by_flush",removedComps.size());  
}

/**
 * Return split levels whose corresponding variable
 * has become zero implied in the solver since the last call of this function. 
 */
void SplittingBranchSelector::getNewZeroImpliedSplits(SplitLevelStack& res)
{
  CALL("SplittingBranchSelector::getNewZeroImpliedSplits");  
  ASS(res.isEmpty());  
  
  if (!_handleZeroImplied) {
    return;
  }    
  
  unsigned maxSatVar = _parent.maxSatVar();
  for(unsigned i=1; i<=maxSatVar; i++) {
    if (!_zeroImplieds[i] && _solver->isZeroImplied(i)) {
      _zeroImplieds[i] = true;
      
      SplitLevel posLvl = _parent.getNameFromLiteral(SATLiteral(i, true));
      SplitLevel negLvl = _parent.getNameFromLiteral(SATLiteral(i, false));
      
      if (_parent.isUsedName(posLvl)) {
        res.push(posLvl);
      }
      if (_parent.isUsedName(negLvl)) {
        res.push(negLvl);
      }
    }
  }
}

//////////////
// Splitter
//////////////

Splitter::Splitter()
: _deleteDeactivated(Options::SplittingDeleteDeactivated::ON), _branchSelector(*this), 
  _haveBranchRefutation(false), _clausesSinceEmpty(0) 
{
  CALL("Splitter::Splitter");
}

Splitter::~Splitter()
{
  CALL("Splitter::~Splitter");

  while(_db.isNonEmpty()) {
    if(_db.top()) {
      delete _db.top();
    }
    _db.pop();
  }
}

const Options& Splitter::getOptions() const
{
  CALL("Splitter::getOptions");
  ASS(_sa);

  return _sa->getOptions();
}

Ordering& Splitter::getOrdering() const
{
  CALL("Splitter::getOrdering");
  ASS(_sa);

  return _sa->getOrdering();
}


void Splitter::init(SaturationAlgorithm* sa)
{
  CALL("Splitter::init");

  _sa = sa;

  const Options& opts = getOptions();
  _branchSelector.init();
  _complBehavior = opts.splittingAddComplementary();
  _nonsplComps = opts.splittingNonsplittableComponents();

  _flushPeriod = opts.splittingFlushPeriod();
  _flushQuotient = opts.splittingFlushQuotient();
  _flushThreshold = sa->getGeneratedClauseCount() + _flushPeriod;

  _congruenceClosure = opts.splittingCongruenceClosure();  
  _fastRestart = opts.splittingFastRestart();
  _deleteDeactivated = opts.splittingDeleteDeactivated();    
}

SplitLevel Splitter::getNameFromLiteral(SATLiteral lit) const
{
  CALL("Splitter::getNameFromLiteral");

  SplitLevel res = getNameFromLiteralUnsafe(lit);
  ASS_L(res, _db.size());
  return res;
}

/**
 * This function can be called with SAT literal for which the split
 * record is not created yet. In this case the result will be larger
 * than the size of _db.
 */
SplitLevel Splitter::getNameFromLiteralUnsafe(SATLiteral lit) const
{
  CALL("Splitter::getNameFromLiteralUnsafe");

  return (lit.var()-1)*2 + (lit.polarity() ? 0 : 1);
}
SATLiteral Splitter::getLiteralFromName(SplitLevel compName) const
{
  CALL("Splitter::getLiteralFromName");
  ASS_L(compName, _db.size());

  unsigned var = compName/2 + 1;
  bool polarity = (compName&1)==0;
  return SATLiteral(var, polarity);
}
void Splitter::collectDependenceLits(SplitSet* splits, SATLiteralStack& acc) const
{
  SplitSet::Iterator sit(*splits);
  while(sit.hasNext()) {
    SplitLevel nm = sit.next();
    acc.push(getLiteralFromName(nm).opposite());
  }
}

Clause* Splitter::getComponentClause(SplitLevel name) const
{
  CALL("Splitter::getComponentClause");
  ASS_L(name,_db.size());
  ASS_NEQ(_db[name],0);

  return _db[name]->component;
}


void Splitter::recordSATClauseForAddition(SATClause* cl, bool branchRefutation)
{
  CALL("Splitter::addSATClause");

  cl = Preprocess::removeDuplicateLiterals(cl);
  if(!cl) {
    return;
  }
  if(branchRefutation) {
    _haveBranchRefutation = true;
    _conflictClausesToBeAdded.push(cl);
  } else {
    _regularClausesToBeAdded.push(cl);
  }  
}

void Splitter::onAllProcessed()
{
  CALL("Splitter::onAllProcessed");

  RSTAT_MCTR_INC("splitter_EmptyAtOnce",_conflictClausesToBeAdded.size());
  RSTAT_MCTR_INC("splitter_callsSinceEmpty",_clausesSinceEmpty);
  _clausesSinceEmpty = 0;
  
  bool flushing = false;
  if(_flushPeriod) {
    if(_haveBranchRefutation) {
      _flushThreshold = _sa->getGeneratedClauseCount()+_flushPeriod;
    }
    if(_sa->getGeneratedClauseCount()>=_flushThreshold && 
            _regularClausesToBeAdded.isEmpty() && _conflictClausesToBeAdded.isEmpty()) {
      flushing = true;
      _flushThreshold = _sa->getGeneratedClauseCount()+_flushPeriod;
      _flushPeriod = static_cast<unsigned>(_flushPeriod*_flushQuotient);
    }
  }

  _haveBranchRefutation = false;

  if(_regularClausesToBeAdded.isEmpty() && _conflictClausesToBeAdded.isEmpty() && !flushing) {
    return;
  }
  static SplitLevelStack toAdd;
  static SplitLevelStack toRemove;
  
  toAdd.reset();
  toRemove.reset();  
  if(flushing) {
    _branchSelector.flush(toAdd, toRemove);
  }
  else {
    _branchSelector.addSatClauses(_regularClausesToBeAdded,_conflictClausesToBeAdded, toAdd, toRemove);
    _regularClausesToBeAdded.reset();
    _conflictClausesToBeAdded.reset();
  }

  static SplitLevelStack newZeroImplied;
  newZeroImplied.reset();
  _branchSelector.getNewZeroImpliedSplits(newZeroImplied);
  
  if(toRemove.isNonEmpty()) {
    removeComponents(toRemove);
  }
  if(toAdd.isNonEmpty()) {
    addComponents(toAdd);
  }

  // now that new activ-ness has been determined  
  // we can put back the fast clauses, if any
  while(_fastClauses.isNonEmpty()) {
    Clause* rcl=_fastClauses.popWithoutDec();

    // TODO: could use a check based on "NumActiveSplits" instead,
    // but would need to maintain them even when _deleteDeactivated == Options::SplittingDeleteDeactivated::ON
    if (allSplitLevelsActive(rcl->splits())) {
      RSTAT_CTR_INC("fast_clauses_restored");
      _sa->addNewClause(rcl);
    } else {
      RSTAT_CTR_INC("fast_clauses_not_restored");
    }
    
    rcl->decRefCnt(); //belongs to _fastClauses.popWithoutDec();
  }  
  
  if (newZeroImplied.isNonEmpty()) {
    processNewZeroImplied(newZeroImplied);
  }  
}


bool Splitter::shouldAddClauseForNonSplittable(Clause* cl, unsigned& compName, Clause*& compCl)
{
  CALL("Splitter::shouldAddClauseForNonSplittable");
  
  //!! this check is important or we might end up looping !!
  if(cl->isComponent()) {    
    return false;
  }

  if(_congruenceClosure != Options::SplittingCongruenceClosure::OFF
      && cl->length()==1 && (*cl)[0]->ground() && cl->splits()->isEmpty()) {
    //we add ground unit clauses if we use congruence closure...
    // (immediately zero implied!)
    compName = tryGetComponentNameOrAddNew(cl->length(), cl->literals(), cl, compCl);
    RSTAT_CTR_INC("ssat_ground_clauses_for_congruence");
    return true;
  }

  if(_nonsplComps==Options::SplittingNonsplittableComponents::NONE) {
    return false;
  }

  if(!tryGetExistingComponentName(cl->length(), cl->literals(), compName, compCl)) {
    bool canCreate;
    switch(_nonsplComps) {
    case Options::SplittingNonsplittableComponents::ALL:
      canCreate = true;
      break;
    case Options::SplittingNonsplittableComponents::ALL_DEPENDENT:
      canCreate = !cl->splits()->isEmpty();
      break;
    case Options::SplittingNonsplittableComponents::KNOWN:
      canCreate = false;
      break;
    default:
      ASSERTION_VIOLATION;
    }
    if(!canCreate) {
      return false;
    }
    RSTAT_CTR_INC("ssat_non_splittable_introduced_components");
    compName = tryGetComponentNameOrAddNew(cl->length(), cl->literals(), cl, compCl);
  }
  ASS_NEQ(cl,compCl);

  // We only reach here if cl already exists as a component

  return true;
}

bool Splitter::handleNonSplittable(Clause* cl)
{
  CALL("Splitter::handleNonSplittable");

  SplitLevel compName;
  Clause* compCl;
  if(!shouldAddClauseForNonSplittable(cl, compName, compCl)) {
    return false;
  }

  if(_nonsplComps==Options::SplittingNonsplittableComponents::NONE) {
    return false;
  }

  SplitSet* sset = cl->splits();
  ASS(sset->size()!=1 || _db[sset->sval()]->component!=cl);
  if(sset->member(compName)) {
    //we derived a component that depends on itself.
    //This derivation is therefore redundant, so we can skip it.
    RSTAT_CTR_INC("ssat_self_dependent_component");
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

  SplitRecord& nameRec = *_db[compName];
  ASS_EQ(nameRec.component,compCl);
  ASS_REP2(compCl->store()==Clause::NONE || compCl->store()==Clause::ACTIVE ||
      compCl->store()==Clause::PASSIVE || compCl->store()==Clause::UNPROCESSED, *compCl, compCl->store());
  if(nameRec.active && compCl->store()==Clause::NONE) {
    //we need to make sure the clause naming the component is present in this case, as the
    //following scenario may lead to incompleteness:
    //  component C is selected and put to unprocessed
    //  clause C' syntactically equal to C is derived and put into simplification container
    //  component C is made redundant by C'
    //  we name C' as C. The sat clause {C} won't lead to addition of C into FO as C is already selected.
    
    compCl->invalidateMyReductionRecords();
    _sa->addNewClause(compCl);
    if ((_deleteDeactivated != Options::SplittingDeleteDeactivated::ON) &&
            !nameRec.children.find(compCl)) {
      // corner case within a corner case:
      // the compCl was already shown unconditionally redundant,
      // but now we must must put it back (TODO: do we really?)
      // so we must also keep track of it
      nameRec.children.push(compCl);
    }    
  }

  recordSATClauseForAddition(nsClause, false);
  return true;
}

/**
 * Takes Clause cl and attempts to split it into Components i.e. produces C1...Cn = cl such that
 * all Ci's have a pairwise disjoint set of variables and no Ci can be split further - the
 * splitting is maximal.
 *
 * Returns true if this is possible and false otherwise. The result is placed in acc.
 *
 * This is implemented using the Union-Find algorithm.
 *
 * Comment by Giles. 
 */
bool Splitter::getComponents(Clause* cl, Stack<LiteralStack>& acc)
{
  CALL("Splitter::getComponents");
  ASS_EQ(acc.size(), 0);

  unsigned clen=cl->length();
  ASS_G(clen,0);

  if(clen<=1) {
    return false;
  }

  //Master literal of an variable is the literal
  //with lowest index, in which it appears.
  static DHMap<unsigned, unsigned, IdentityHash> varMasters;
  varMasters.reset();
  IntUnionFind components(clen);

  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    VariableIterator vit(lit);
    while(vit.hasNext()) {
      unsigned master=varMasters.findOrInsert(vit.next().var(), i);
      if(master!=i) {
	components.doUnion(master, i);
      }
    }
  }
  components.evalComponents();

  unsigned compCnt=components.getComponentCount();

  if(compCnt==1) {
    return false;
  }

  env.statistics->splitClauses++;
  env.statistics->splitComponents+=compCnt;

  IntUnionFind::ComponentIterator cit(components);
  ASS(cit.hasNext());
  while(cit.hasNext()) {
    IntUnionFind::ElementIterator elit=cit.next();

    acc.push(LiteralStack());

    while(elit.hasNext()) {
      int litIndex=elit.next();
      Literal* lit = (*cl)[litIndex];

      acc.top().push(lit);
    }
  }
  ASS_EQ(acc.size(),compCnt);
  return true;
}


/**
 * Attempt to split clause @b cl, and return true if successful
 */
bool Splitter::doSplitting(Clause* cl)
{
  CALL("Splitter::doSplitting");

  if (_fastRestart && _conflictClausesToBeAdded.size() > 0) {
    _fastClauses.push(cl);
    return true; // the clause is ours now
  }
  
  if (_conflictClausesToBeAdded.size() > 0) {
    _clausesSinceEmpty++;
  }
  
  static Stack<LiteralStack> comps;
  comps.reset();
  // fills comps with components, returning if not splittable
  if(!getComponents(cl, comps)) {
    return handleNonSplittable(cl);
  }

  static SATLiteralStack satClauseLits;
  satClauseLits.reset();

  // Add literals for existing constraints 
  collectDependenceLits(cl->splits(), satClauseLits);

  ClauseList* namePremises = 0;

  unsigned compCnt = comps.size();
  for(unsigned i=0; i<compCnt; ++i) {
    const LiteralStack& comp = comps[i];
    Clause* compCl;
    SplitLevel compName = tryGetComponentNameOrAddNew(comp, cl, compCl);
    SATLiteral nameLit = getLiteralFromName(compName);
    satClauseLits.push(nameLit);
    ClauseList::push(compCl, namePremises);
  }

  SATClause* splitClause = SATClause::fromStack(satClauseLits);
  splitClause->setInference(new FOSplittingInference(cl, namePremises));

  recordSATClauseForAddition(splitClause, false);

  env.statistics->satSplits++;
  return true;
}

/**
 * Uses _componentIdx to search for an existing name for the component represented by @b lits
 *
 * @param size number of literals in component
 * @param lits literals of component
 * @param comp the existing propositional name (SplitLevel) for this component - to be filled 
 * @param compCl the existing clause for this component - to be filled
 * @return True if the component already exists
 *
 * @author Giles
 */
bool Splitter::tryGetExistingComponentName(unsigned size, Literal* const * lits, SplitLevel& comp, Clause*& compCl)
{
  CALL("Splitter::tryGetExistingComponentName");

  ClauseIterator existingComponents;
  { 
    TimeCounter tc(TC_SPLITTING_COMPONENT_INDEX_USAGE);
    existingComponents = _componentIdx.retrieveVariants(lits, size);
  }

  if(!existingComponents.hasNext()) {
    return false;
  }
  compCl = existingComponents.next();
  ASS(!existingComponents.hasNext());
  comp = _compNames.get(compCl);
  return true;
}

/**
 * Records a new component. This involves
 * - Building a new Clause for the component as a SAT_SPLITTING_COMPONENT
 * - Create a SplitRecord for the component
 * - Record the name in the splits of the clause
 * - Insert the clause into _componentIdx for variant checking later
 * - Insert the clause with the name into _compNames for lookup later
 *
 * @param name The propositional name for the component to add
 * @param size The number of literals in the component to add
 * @param lits The literals in the component to add
 * @param orig The original clause i.e. the one that we are splitting
 *
 * Comment by Giles.
 */
Clause* Splitter::buildAndInsertComponentClause(SplitLevel name, unsigned size, Literal* const * lits, Clause* orig)
{
  CALL("Splitter::buildAndInsertComponentClause");
  ASS_EQ(_db[name],0);

  Unit::InputType inpType = orig ? orig->inputType() : Unit::AXIOM;
  Clause* compCl = Clause::fromIterator(getArrayishObjectIterator(lits, size), inpType, 
          new Inference(Inference::SAT_SPLITTING_COMPONENT));

  compCl->setAge(orig ? orig->age() : AGE_NOT_FILLED);

  _db[name] = new SplitRecord(compCl);
  compCl->setSplits(SplitSet::getSingleton(name));
  compCl->setComponent(true);

  if (_deleteDeactivated != Options::SplittingDeleteDeactivated::ON) {
    // in this mode, compCl is assumed to be a child since the beginning of times
    _db[name]->children.push(compCl);
    
    // (with _deleteDeactivated on, compCl is always inserted anew on activation)
  }
  
  {
    TimeCounter tc(TC_SPLITTING_COMPONENT_INDEX_MAINTENANCE);
    _componentIdx.insert(compCl);
  }
  _compNames.insert(compCl, name);

  return compCl;
}

SplitLevel Splitter::addNonGroundComponent(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl)
{
  CALL("Splitter::addNonGroundComponent");
  ASS_REP(_db.size()%2==0, _db.size());
  ASS_G(size,0);
  ASS(forAll(getArrayishObjectIterator(lits, size), 
          [] (Literal* l) { return !l->ground(); } )); //none of the literals can be ground

  SATLiteral posLit(_sat2fo.createSpareSatVar(), true);
  SplitLevel compName = getNameFromLiteralUnsafe(posLit);
  ASS_EQ(compName&1,0); //positive levels are even
  ASS_GE(compName,_db.size());
  _db.push(0);
  _db.push(0);
  ASS_L(compName,_db.size());

  _branchSelector.updateVarCnt();
  _branchSelector.considerPolarityAdvice(posLit);

  compCl = buildAndInsertComponentClause(compName, size, lits, orig);

  return compName;
}

SplitLevel Splitter::addGroundComponent(Literal* lit, Clause* orig, Clause*& compCl)
{
  CALL("Splitter::addGroundComponent");
  ASS_REP(_db.size()%2==0, _db.size());
  ASS(lit->ground());

  SATLiteral satLit = _sat2fo.toSAT(lit);
  SplitLevel compName = getNameFromLiteralUnsafe(satLit);

  if(compName>=_db.size()) {
    _db.push(0);
    _db.push(0);
  }
  else {
    ASS_EQ(_complBehavior,Options::SplittingAddComplementary::NONE); 
    //otherwise the complement would have been created below ...
    // ... in the respective previous pass through this method 
  }
  ASS_L(compName,_db.size());

  if(_complBehavior!=Options::SplittingAddComplementary::NONE) {
    //we insert both literal and its negation
    unsigned oppName = compName^1;
    ASS_L(oppName,_db.size());
    Literal* opposite = Literal::complementaryLiteral(lit);
    buildAndInsertComponentClause(oppName, 1, &opposite, orig);
  }
  compCl = buildAndInsertComponentClause(compName, 1, &lit, orig);

  _branchSelector.updateVarCnt();
  _branchSelector.considerPolarityAdvice(satLit);

  return compName;
}

/**
 * @param orig original clause (one being split) used to determine input type of the component.
 *             Can be zero, in that case the input type is Unit::AXIOM
 * @param comp Component (Record) that we're getting the name for
 * @param compCl The clause that will be used to represent this component - to be filled
 *
 * @return the propositional name for the Clause (to be passed to the SAT solver)
 */
SplitLevel Splitter::tryGetComponentNameOrAddNew(const LiteralStack& comp, Clause* orig, Clause*& compCl)
{
  CALL("Splitter::getComponentName/3");
  return tryGetComponentNameOrAddNew(comp.size(), comp.begin(), orig, compCl);
}

/**
 * @param orig original clause (one being split) used to determine input type of the component.
 *             Can be zero, in that case the input type is Unit::AXIOM
 * @param size The number of literals in the component
 * @param lits The component to be named (as an array of literals)
 * @param compCl The clause that will be used to represent this component - to be filled
 *
 * @return the propositional name for the Clause (to be passed to the SAT solver) 
 */
SplitLevel Splitter::tryGetComponentNameOrAddNew(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl)
{
  CALL("Splitter::getComponentName/4");

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

static const int NOT_WORTH_REINTRODUCING = 0;

/**
 * Assign the @b SplitSet @b splits to the clause @b cl.
 */
void Splitter::assignClauseSplitSet(Clause* cl, SplitSet* splits)
{
  CALL("Splitter::assignClauseSplitSet");
  ASS(!cl->splits());
    
  cl->setSplits(splits);

  //update "children" field of relevant SplitRecords
  SplitSet::Iterator bsit(*splits);
  bool should_reintroduce = false;
  int cl_weight = cl->weight();
  while(bsit.hasNext()) {
    SplitLevel slev=bsit.next();
    _db[slev]->children.push(cl);    
    if (cl_weight <= _db[slev]->component->weight()) {
      should_reintroduce = true;
    }
  }  
  
  /**
   * Heuristic idea -- only if the clause is lighter than at least
   * one of the component clauses on which it depends, 
   * it will be kept for reintroduction.
   */
  if (_deleteDeactivated != Options::SplittingDeleteDeactivated::ON) {
    cl->setNumActiveSplits(
      (_deleteDeactivated == Options::SplittingDeleteDeactivated::OFF || should_reintroduce) ? 
        splits->size() : NOT_WORTH_REINTRODUCING);
  }
}

/**
 * Register the reduction of the @b cl clause
 *
 * At this stage we also check for zero-implied literals and remove
 * them if found, this is safe as we no longer rely on them
 */
void Splitter::onClauseReduction(Clause* cl, ClauseIterator premises, Clause* replacement)
{
  CALL("Splitter::onClauseReduction");
  ASS(cl);

  if(!premises.hasNext()) {
    ASS(!replacement || cl->splits()==replacement->splits());
    return;
  }

  SplitSet* unionAll;
  if(replacement) {
    unionAll = replacement->splits();
    ASS(forAll(premises, 
            [replacement,this] (Clause* premise) { 
              //SplitSet* difference = premise->splits()->subtract(replacement->splits());
              //if(difference->isEmpty()) return true; // isSubsetOf true
              // Now check if those in the difference are zero implied
              //SplitSet::Iterator dsit(*difference);
              //while(dsit.hasNext()){
              //  SplitLevel sl = dsit.next();
                // check if zero-implied
              //  SATLiteral sat_lit = getLiteralFromName(sl);
              //  if(!_branchSelector.isZeroImplied(sat_lit)) return false;
              //}
              //return true; // all okay              
              return premise->splits()->isSubsetOf(replacement->splits()); 
            } ));
  } else {
    Clause* premise0 = premises.next();
    unionAll=premise0->splits();
    while(premises.hasNext()) {
      Clause* premise=premises.next();
      ASS(premise);
      unionAll=unionAll->getUnion(premise->splits());
    }
  }
  SplitSet* diff=unionAll->subtract(cl->splits());      
        
  ASS(allSplitLevelsActive(diff));

  if(diff->isEmpty()) {
    // unconditionally reduced
    if (_deleteDeactivated != Options::SplittingDeleteDeactivated::ON) {
      // let others know not to keep the clause in children
      cl->setNumActiveSplits(NOT_WORTH_REINTRODUCING);
    }
        
    return;
  }
  // else freeze clause

  // TODO: keep statistics in release ?
//#if VDEBUG
  cl->incFreezeCount();
  RSTAT_MCTR_INC("frozen clauses",cl->getFreezeCount());
  RSTAT_CTR_INC("total_frozen");
//#endif

  cl->invalidateMyReductionRecords();
  SplitSet::Iterator dit(*diff);
  while(dit.hasNext()) {
    SplitLevel slev=dit.next();
    _db[slev]->addReduced(cl);
  }
}

bool Splitter::allSplitLevelsActive(SplitSet* s)
{
  CALL("Splitter::allSplitLevelsActive");

  SplitSet::Iterator sit(*s);
  while(sit.hasNext()) {
    SplitLevel lev=sit.next();
    ASS_REP(lev<_db.size(), lev);
    ASS_REP(_db[lev]!=0, lev);
    if (!_db[lev]->active) {
      return false;
    }
  }
  return true;
}

void Splitter::onNewClause(Clause* cl)
{
  CALL("Splitter::onNewClause");

  //For now just record if cl is in the variant index
  // i.e. is a component
  //TODO - if it is then
  // (a) if it is true it can be immediately frozen
  // (b) if it is false it can be immediately passed to the SAT
  //      solver and kill the current model
  //bool isComponent = false;
  //{
  //  //TODO - would it be better to use tryGetExistingComponent here?
  //  TimeCounter tc(TC_SPLITTING_COMPONENT_INDEX_USAGE);
  //  isComponent = _componentIdx.retrieveVariants(cl).hasNext();
  //}
  //if(isComponent){
  //	RSTAT_CTR_INC("New Clause is a Component");
  //}

  if(!cl->splits()) {
    SplitSet* splits=getNewClauseSplitSet(cl);
    assignClauseSplitSet(cl, splits);
  }

  ASS(allSplitLevelsActive(cl->splits()));  
}

/**
 * Return a split set of a new clause
 *
 * Assumes that clauses referred to by cl->inference() object
 * are actual premises of @b cl. (This holds when BDDs are not
 * used.)
 */
SplitSet* Splitter::getNewClauseSplitSet(Clause* cl)
{
  CALL("Splitter::getNewClauseSplitSet");

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


Splitter::SplitRecord::~SplitRecord()
{
  CALL("Splitter::SplitRecord::~SplitRecord");
  component->decRefCnt();
  while(reduced.isNonEmpty()) {
    Clause* cl = reduced.pop().clause;
    cl->decRefCnt();
  }
}

/**
 * Add a reduced clause to the @b SplitRecord object.
 */
void Splitter::SplitRecord::addReduced(Clause* cl)
{
  CALL("Splitter::SplitRecord::addReduced");

  cl->incRefCnt(); //dec when popped from the '_db[slev]->reduced' stack in backtrack method
  reduced.push(ReductionRecord(cl));
}

bool Splitter::handleEmptyClause(Clause* cl)
{
  CALL("Splitter::handleEmptyClause");

  if(cl->splits()->isEmpty()) {
    return false;
  }

  static SATLiteralStack conflictLits;
  conflictLits.reset();

  collectDependenceLits(cl->splits(), conflictLits);
  SATClause* confl = SATClause::fromStack(conflictLits);
  confl->setInference(new FOConversionInference(cl));
  
  RSTAT_MCTR_INC("sspl_confl_len", confl->length());

  recordSATClauseForAddition(confl, true);

  env.statistics->satSplitRefutations++;
  return true;
}


void Splitter::addComponents(const SplitLevelStack& toAdd)
{
  CALL("Splitter::addComponents");

  SplitLevelStack::ConstIterator slit(toAdd);
  while(slit.hasNext()) {
    SplitLevel sl = slit.next();
    SplitRecord* sr = _db[sl];
    ASS(sr);
    ASS(!sr->active);
    sr->active = true;
    
    if (_deleteDeactivated == Options::SplittingDeleteDeactivated::ON) {
      ASS(sr->children.isEmpty());
      //we need to put the component clause among children, 
      //so that it is backtracked when we remove the component
      sr->children.push(sr->component);
      _sa->addNewClause(sr->component);
    } else {
      // children were kept, so we just put them back
      RCClauseStack::Iterator chit(sr->children);
      unsigned reactivated_cnt = 0;
      while (chit.hasNext()) {
        Clause* cl = chit.next();
        cl->incNumActiveSplits();
        if (cl->getNumActiveSplits() == (int)cl->splits()->size()) {
          reactivated_cnt++;
          _sa->addNewClause(cl);
          //check that restored clause does not depend on inactive splits
          ASS(allSplitLevelsActive(cl->splits()));
        }
      }
      RSTAT_MCTR_INC("reactivated clauses",reactivated_cnt);      
    }
  }
}

/**
 * Perform backtracking of split levels in @c toRemove.
 *
 * Can be called only when there are no unprocessed clauses left.
 * This is to allow for easy clause removal from the saturation algorithm.
 */
void Splitter::removeComponents(const SplitLevelStack& toRemove)
{
  CALL("Splitter::removeComponents");
  ASS(_sa->clausesFlushed());
  
  SplitSet* backtracked = SplitSet::getFromArray(toRemove.begin(), toRemove.size());

  // ensure all children are backtracked
  // i.e. removed from _sa and reference counter dec
  SplitSet::Iterator blit(*backtracked);
  while(blit.hasNext()) {
    SplitLevel bl=blit.next();
    SplitRecord* sr=_db[bl];
    ASS(sr);
    
    RCClauseStack::DelIterator chit(sr->children);
    while (chit.hasNext()) {
      Clause* ccl=chit.next();
      ASS(ccl->splits()->member(bl));
      if(ccl->store()!=Clause::NONE) {
        _sa->removeActiveOrPassiveClause(ccl);
        ASS_EQ(ccl->store(), Clause::NONE);
      }
      ccl->invalidateMyReductionRecords();
      ccl->decNumActiveSplits();
      if (ccl->getNumActiveSplits() < NOT_WORTH_REINTRODUCING) {
        RSTAT_CTR_INC("unworthy child removed");
        chit.del();
      }
    }
    
    if (_deleteDeactivated == Options::SplittingDeleteDeactivated::ON) {
      sr->children.reset();
    }
  }

  // perform unfreezing  
    
  // pick all reduced clauses (if the record relates to most recent reduction)
  // and them add back to _sa using addNewClause - this will get put to unprocessed
  SplitSet::Iterator blit2(*backtracked);
  while(blit2.hasNext()) {
    SplitLevel bl=blit2.next();
    SplitRecord* sr=_db[bl];

    while(sr->reduced.isNonEmpty()) {
      ReductionRecord rrec=sr->reduced.pop();
      Clause* rcl=rrec.clause;
      if(rcl->validReductionRecord(rrec.timestamp)) {
        ASS(!rcl->splits()->hasIntersection(backtracked));      
        ASS_EQ(rcl->store(), Clause::NONE);
        
        rcl->invalidateMyReductionRecords(); // to make sure we don't unfreeze this clause a second time
        _sa->addNewClause(rcl);
              
        // TODO: keep statistics in release ?
        RSTAT_MCTR_INC("unfrozen clauses",rcl->getFreezeCount());
        RSTAT_CTR_INC("total_unfrozen");
#if VDEBUG      
        //check that restored clause does not depend on inactive splits
        ASS(allSplitLevelsActive(rcl->splits()));
#endif
        
      }
      rcl->decRefCnt(); //inc when pushed on the 'sr->reduced' stack in Splitter::SplitRecord::addReduced
    }

    ASS(sr->active);
    sr->active = false;
  }
}

/**
 * A zero implied split will never change from active to non-active
 * (or the other way round) anymore. We can reduce the bookkeeping 
 * and remove dependencies on the split. 
 * 
 * Currently, we only handle active zero implied splits.
 * 
 */
void Splitter::processNewZeroImplied(const SplitLevelStack& newZeroImplied)
{
  CALL("Splitter::processNewZeroImplied");
  
  SplitLevelStack::ConstIterator slit(newZeroImplied);
  while(slit.hasNext()) {
    SplitLevel sl = slit.next();
    SplitRecord* sr = _db[sl];
    ASS(sr);
    
    if (sr->active) {
      RSTAT_CTR_INC("zero implied active"); // forever active from now on
      
      SplitSet* myLevelSet = SplitSet::getSingleton(sl);
      // we don't need to maintain children anymore ...
      while(sr->children.isNonEmpty()) {
        Clause* ccl=sr->children.popWithoutDec();
        ASS(ccl->splits()->member(sl));
        ccl->setSplits(ccl->splits()->subtract(myLevelSet),true);
        if (_deleteDeactivated != Options::SplittingDeleteDeactivated::ON) { //NumActiveSplits being maintained
          ccl->decNumActiveSplits();
        }        
        ccl->decRefCnt(); //decrease corresponding to sr->children.popWithoutDec()
      }

      // ... nor the reduction records
      while(sr->reduced.isNonEmpty()) {
        ReductionRecord rrec=sr->reduced.pop();
        Clause* rcl=rrec.clause;
        rcl->decRefCnt(); //inc when pushed on the 'sr->reduced' stack in Splitter::SplitRecord::addReduced
      }
      // TODO: release also sr->component ?                
    } else {
      RSTAT_CTR_INC("zero implied !active"); // forever !active from now on
      
      ASS(sr->children.isEmpty() || _deleteDeactivated != Options::SplittingDeleteDeactivated::ON);
      while(sr->children.isNonEmpty()) {
        Clause* ccl=sr->children.popWithoutDec();
        ccl->setNumActiveSplits(NOT_WORTH_REINTRODUCING);
        ccl->decRefCnt(); //decrease corresponding to sr->children.popWithoutDec()
      }
      
      ASS(sr->reduced.isEmpty());
    }
  }
}

}
