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
#include "DP/SimpleCongruenceClosure.hpp"

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
  _zeroOpt = _parent.getOptions().zeroOpt();

  switch(_parent.getOptions().satSolver()){
    case Options::BUFFERED_VAMPIRE:
      _solver = new BufferedSolver(new TWLSolver(_parent.getOptions(),true));
      break;
    case Options::VAMPIRE:  
      _solver = new TWLSolver(_parent.getOptions(), true);
      break;
    case Options::BUFFERED_LINGELING: 
      _solver = new BufferedSolver(new LingelingInterfacing(_parent.getOptions(), true));
      break;
    case Options::LINGELING: 
      _solver = new LingelingInterfacing(_parent.getOptions(), true);
      break;
    case Options::BUFFERED_MINISAT:
      _solver = new BufferedSolver(new MinisatInterfacing(_parent.getOptions(),true));
      break;
    case Options::MINISAT:
      _solver = new MinisatInterfacing(_parent.getOptions(),true);
      break;      
    default:
      ASSERTION_VIOLATION_REP(_parent.getOptions().satSolver());
  }

  switch(_parent.getOptions().splittingModel()){
    case Options::SM_TOTAL:
      // Do nothing - we don't want to minimise the model
      break;
    case Options::SM_MIN_ALL:
      _solver = new MinimizingSolver(_solver.release(),false);
      break;
    case  Options::SM_MIN_SCO:
      _solver = new MinimizingSolver(_solver.release(),true);
      break;
    default:
      ASSERTION_VIOLATION_REP(_parent.getOptions().splittingModel());
  }


#if DEBUG_MIN_SOLVER
  _solver = new Test::CheckedSatSolver(_solver.release());
#endif

  //Giles. Currently false by default.
  if(_parent.getOptions().splittingCongruenceClosure()) {
    // ASSERTION_VIOLATION_REP("Is this ever turned on?");
    _dp = new ShortConflictMetaDP(new DP::SimpleCongruenceClosure(), _parent.satNaming(), *_solver);
  }
}

void SplittingBranchSelector::updateVarCnt()
{
  CALL("SplittingBranchSelector::ensureVarCnt");

  unsigned satVarCnt = _parent.maxSatVar()+1;
  unsigned splitLvlCnt = _parent.splitLevelCnt();

  _solver->ensureVarCnt(satVarCnt);
  _selected.expand(splitLvlCnt);
}

void SplittingBranchSelector::handleSatRefutation(SATClause* ref)
{
  CALL("SplittingBranchSelector::handleSatRefutation");

  UnitList* prems = SATInference::getFOPremises(ref);
  Inference* foInf = new InferenceMany(Inference::SAT_SPLITTING_REFUTATION, prems);
  Clause* foRef = Clause::fromIterator(LiteralIterator::getEmpty(), Unit::CONJECTURE, foInf);
  throw MainLoop::RefutationFoundException(foRef);
}

void SplittingBranchSelector::processDPConflicts()
{
  CALL("SplittingBranchSelector::processDPConflicts");
  ASS(_solver->getStatus()==SATSolver::SATISFIABLE || _solver->getStatus()==SATSolver::UNSATISFIABLE);

  if(!_dp || _solver->getStatus()==SATSolver::UNSATISFIABLE) {
    return;
  }

  TimeCounter tc(TC_CONGRUENCE_CLOSURE);

  SAT2FO& s2f = _parent.satNaming();
  static LiteralStack gndAssignment;
  static LiteralStack unsatCore;

  static SATClauseStack conflictClauses;

  while(_solver->getStatus()==SATSolver::SATISFIABLE) {
    gndAssignment.reset(); // Martin. in fact, not ground. Filtering based on gndness happens inside dp
    s2f.collectAssignment(*_solver, gndAssignment);

    _dp->reset();
    _dp->addLiterals(pvi( LiteralStack::ConstIterator(gndAssignment) ));
    DecisionProcedure::Status dpStatus = _dp->getStatus(true);
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

    {
    	TimeCounter tca(TC_SAT_SOLVER);
      // We do not use conflict clauses in the partial model (hence the last false here below)     
    	_solver->addClauses(pvi( SATClauseStack::Iterator(conflictClauses) ),false,false);
    }

    RSTAT_CTR_INC("ssat_dp_conflict");
    RSTAT_CTR_INC_MANY("ssat_dp_conflict_clauses",conflictClauses.size());
  }
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

  TimeCounter tc(TC_SPLITTING_COMPONENT_SELECTION);

  RSTAT_CTR_INC_MANY("ssat_sat_clauses",regularClauses.size()+conflictClauses.size());
  {
    TimeCounter tc1(TC_SAT_SOLVER);
    // We do use regular split clauses in the partial model ...
    _solver->addClauses(pvi( SATClauseStack::ConstIterator(regularClauses) ), false,true);
    // ... but not the clauses derived from conflicts
    _solver->addClauses(pvi( SATClauseStack::ConstIterator(conflictClauses) ), false,false);
    processDPConflicts();
  }

  if(_solver->getStatus()==SATSolver::UNSATISFIABLE) {
    SATClause* satRefutation = _solver->getRefutation();
    handleSatRefutation(satRefutation); // noreturn!
  }
  ASS_EQ(_solver->getStatus(),SATSolver::SATISFIABLE);

  unsigned maxSatVar = _parent.maxSatVar();
  unsigned _usedcnt=0; // for the statistics below
  for(unsigned i=1; i<=maxSatVar; i++) {
    SATSolver::VarAssignment asgn = _solver->getAssignment(i);            
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
  
  if(_solver->getStatus()==SATSolver::UNKNOWN) {    
  	TimeCounter tca(TC_SAT_SOLVER);
    _solver->addClauses(SATClauseIterator::getEmpty()); // Martin: just to get a status? Evil!
  } 
  ASS_EQ(_solver->getStatus(), SATSolver::SATISFIABLE); 
  _solver->randomizeAssignment();

  processDPConflicts(); // Why after the randomization?
  ASS_EQ(_solver->getStatus(), SATSolver::SATISFIABLE);

  unsigned maxSatVar = _parent.maxSatVar();
  unsigned _usedcnt=0; // for the statistics below
  for(unsigned i=1; i<=maxSatVar; i++) {
    SATSolver::VarAssignment asgn = _solver->getAssignment(i);
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

//////////////
// Splitter
//////////////

Splitter::Splitter()
: _branchSelector(*this), _haveBranchRefutation(false), _clausesSinceEmpty(0)
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

  if(toRemove.isNonEmpty()) {
    removeComponents(toRemove);
  }
  if(toAdd.isNonEmpty()) {
    addComponents(toAdd);
  }
}


bool Splitter::shouldAddClauseForNonSplittable(Clause* cl, unsigned& compName, Clause*& compCl)
{
  CALL("Splitter::shouldAddClauseForNonSplittable");

  SplitSet* sset = cl->splits();
  //!! this check is important or we might end up looping !!
  if(sset->size()==1 && _db[sset->sval()]->component==cl) {
    //the clause is already a component
    return false;
  }

  if(_congruenceClosure && cl->length()==1 && (*cl)[0]->ground() && cl->splits()->isEmpty()) {
    //we add ground unit clauses if we use congruence closure...
    // (immediately zero implied!)
    compName = tryGetComponentNameOrAddNew(cl->length(), cl->literals(), cl, compCl);
    RSTAT_CTR_INC("ssat_ground_clauses_for_congruence");
    return true;
  }

  if(_nonsplComps==Options::SNS_NONE) {
    return false;
  }

  if(!tryGetExistingComponentName(cl->length(), cl->literals(), compName, compCl)) {
    bool canCreate;
    switch(_nonsplComps) {
    case Options::SNS_ALL:
      canCreate = true;
      break;
    case Options::SNS_ALL_DEPENDENT:
      canCreate = !sset->isEmpty();
      break;
    case Options::SNS_KNOWN:
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

  if(_nonsplComps==Options::SNS_NONE) {
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
  _branchSelector.clearZeroImpliedSplits(cl);
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

  _db[name] = new SplitRecord(compCl);

  compCl->setSplits(SplitSet::getSingleton(name));

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
    ASS_EQ(_complBehavior,Options::SAC_NONE); 
    //otherwise the complement would have been created below ...
    // ... in the respective previous pass through this method 
  }
  ASS_L(compName,_db.size());

  if(_complBehavior!=Options::SAC_NONE) {
    //we insert both literal and its negation
    unsigned oppName = compName^1;
    ASS_L(oppName,_db.size());
    Literal* opposite = Literal::complementaryLiteral(lit);
    buildAndInsertComponentClause(oppName, 1, &opposite, orig);
  }
  compCl = buildAndInsertComponentClause(compName, 1, &lit, orig);

  _branchSelector.updateVarCnt();

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
  while(bsit.hasNext()) {
    SplitLevel slev=bsit.next();
    _db[slev]->children.push(cl);
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

  _branchSelector.clearZeroImpliedSplits(cl);

  if(!premises.hasNext()) {
    ASS(!replacement || cl->splits()==replacement->splits());
    return;
  }

  SplitSet* unionAll;
  if(replacement) {
    unionAll = replacement->splits();
    ASS(forAll(premises, 
            [replacement] (Clause* premise) { 
              return premise->splits()->isSubsetOf(replacement->splits()); 
            } ));
    /* also clearZeroImpliedSplits has been called on premises when replacement 
     * got it's splits() assigned in onNewClause */            
  } else {
    Clause* premise0 = premises.next();
    _branchSelector.clearZeroImpliedSplits(premise0);
    unionAll=premise0->splits();
    while(premises.hasNext()) {
      Clause* premise=premises.next();
      ASS(premise);
      _branchSelector.clearZeroImpliedSplits(premise);
      unionAll=unionAll->getUnion(premise->splits());
    }
  }
  SplitSet* diff=unionAll->subtract(cl->splits());      
        
#if VDEBUG
  assertSplitLevelsActive(diff);
#endif

  if(diff->isEmpty()) {
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

void SplittingBranchSelector::clearZeroImpliedSplits(Clause* cl)
{ 
  CALL("Splitter::clearZeroImpliedSplits");

  if(!_zeroOpt) return;

  SplitLevel this_level;
  bool has_level = _parent.getSplitLevelFromClause(cl,this_level);

  SplitSet* rem=SplitSet::getEmpty();
  SplitSet::Iterator sit(*(cl->splits()));
  while(sit.hasNext()){
    SplitLevel level = sit.next();
    if(has_level && level==this_level) continue;
    SATLiteral lit = _parent.getLiteralFromName(level);
    // We're asking if the current assignment of this var is zero implied
    // We can assume that the assignment is consistent with this lit as it
    // is currently asserted
    if(_solver->isZeroImplied(lit.var())){
      //TODO use a stack for rem instead
      rem = rem->getUnion(SplitSet::getSingleton(level));
      //cout << " will clear " << level << endl;
    }
  }
  if(!rem->isEmpty()){
    //cout << "clearing from " << cl << " with level " << _parent._compNames.get(cl) << endl;
    RSTAT_CTR_INC("clearedZeroImpliedSplits");
    cl->setSplits(cl->splits()->subtract(rem),true);
  }
}

void Splitter::assertSplitLevelsActive(SplitSet* s)
{
  CALL("Splitter::assertSplitLevelsActive");

  SplitSet::Iterator sit(*s);
  while(sit.hasNext()) {
    SplitLevel lev=sit.next();
    ASS_REP(lev<_db.size(), lev);
    ASS_REP(_db[lev]!=0, lev);
    ASS_REP(_db[lev]->active, lev);
  }
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

#if VDEBUG
  assertSplitLevelsActive(cl->splits());
#endif
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
    _branchSelector.clearZeroImpliedSplits(prem);
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
void Splitter::removeComponents(const SplitLevelStack& toRemove)
{
  CALL("Splitter::removeComponents");
  ASS(_sa->clausesFlushed());

  /* Martin: for marking:
   * 1) to remove each of the children only once
   * 2) to restore each reduced only once
   */
  Clause::requestAux();  
  
  static RCClauseStack restored;
  ASS(restored.isEmpty());  

  SplitSet* backtracked = SplitSet::getFromArray(toRemove.begin(), toRemove.size());

  // ensure all children are backtracked
  // i.e. removed from _sa and reference counter dec
  SplitSet::Iterator blit(*backtracked);
  while(blit.hasNext()) {
    SplitLevel bl=blit.next();
    SplitRecord* sr=_db[bl];
    ASS(sr);

    while(sr->children.isNonEmpty()) {
      Clause* ccl=sr->children.popWithoutDec();
      if(!ccl->hasAux()) {
	ASS(ccl->splits()->member(bl));
	if(ccl->store()!=Clause::NONE) {
	  _sa->removeActiveOrPassiveClause(ccl);
	  ASS_EQ(ccl->store(), Clause::NONE);
	}
	ccl->setAux(0);
	ccl->invalidateMyReductionRecords();
      }
      ccl->decRefCnt(); //decrease corresponding to sr->children.popWithoutDec()
    }
  }

  // perform unfreezing

  // add all reduced clauses to restored (if the record relates to most recent reduction)
  SplitSet::Iterator blit2(*backtracked);
  while(blit2.hasNext()) {
    SplitLevel bl=blit2.next();
    SplitRecord* sr=_db[bl];

    while(sr->reduced.isNonEmpty()) {
      ReductionRecord rrec=sr->reduced.pop();
      Clause* rcl=rrec.clause;
      if(rcl->validReductionRecord(rrec.timestamp)) {                            
        restored.push(rcl);
      }
      rcl->decRefCnt(); //inc when pushed on the 'sr->reduced' stack in Splitter::SplitRecord::addReduced
    }

    ASS(sr->active);
    sr->active = false;
  }

  // add back to _sa using addNewClause - this will get put to unprocessed
  while(restored.isNonEmpty()) {
    Clause* rcl=restored.popWithoutDec();
    if(!rcl->hasAux()) {
      ASS(!rcl->splits()->hasIntersection(backtracked));
      rcl->setAux(0);
      ASS_EQ(rcl->store(), Clause::NONE);
      rcl->invalidateMyReductionRecords();      
      _sa->addNewClause(rcl);

      // TODO: keep statistics in release ?
      RSTAT_MCTR_INC("unfrozen clauses",rcl->getFreezeCount());
      RSTAT_CTR_INC("total_unfrozen");
#if VDEBUG      
      //check that restored clause does not depend on inactive splits
      assertSplitLevelsActive(rcl->splits());
#endif
    }
    rcl->decRefCnt(); //belongs to restored.popWithoutDec();
  }

  Clause::releaseAux();
}

}
