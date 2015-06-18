/**
 * @file TWLSolver.cpp
 * Implements class TWLSolver.
 */


#include "Debug/Assertion.hpp"

#include "Lib/TimeCounter.hpp"
#include "Lib/Array.hpp"
#include "Lib/ArrayMap.hpp"
#include "Lib/BinaryHeap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Lib/Timer.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "SATClause.hpp"
#include "SATInference.hpp"
#include "SATLiteral.hpp"

#include "RestartStrategy.hpp"
#include "VariableSelector.hpp"
#include "ClauseDisposer.hpp"

#include "TWLSolver.hpp"

#undef LOGGING
#define LOGGING 0

#if LOGGING
#define LOG1(arg) cout << arg << endl;
#define LOG2(a1,a2) cout << a1 << a2 << endl;
#define LOG3(a1,a2,a3) cout << a1 << a2 << a3 << endl;
#else
#define LOG1(arg)
#define LOG2(a1,a2)
#define LOG3(a1,a2,a3)
#endif

namespace SAT
{

using namespace Lib;

TWLSolver::TWLSolver(const Options& opt, bool generateProofs)
: _generateProofs(generateProofs), _status(SATISFIABLE), _assignment(0), _assignmentLevels(0),
_windex(0), _varCnt(0), _level(1), _assumptionsAdded(false), _assumptionCnt(0), _unsatisfiableAssumptions(false)
{
  switch(opt.satVarSelector()) {
  case Options::SatVarSelector::ACTIVE:
    _variableSelector = new ActiveVariableSelector(*this, Options::Niceness::NONE, opt.satVarActivityDecay());
    break;
  case Options::SatVarSelector::NICENESS:
    //_variableSelector = new ArrayNicenessVariableSelector(*this);
    _variableSelector = new ActiveVariableSelector(*this, opt.nicenessOption(), opt.satVarActivityDecay());
    break;
  case Options::SatVarSelector::RECENTLY_LEARNT:
    _variableSelector = new RLCVariableSelector(*this);
    break;
  }

//  _variableSelector = new AlternatingVariableSelector(*this, new ActiveVariableSelector(*this), new ArrayActiveVariableSelector(*this));


  switch(opt.satRestartStrategy()) {
  case Options::SatRestartStrategy::FIXED:
    _restartStrategy = new FixedRestartStrategy(opt.satRestartFixedCount());
    break;
  case Options::SatRestartStrategy::GEOMETRIC:
    _restartStrategy = new GeometricRestartStrategy(opt.satRestartGeometricInit(), opt.satRestartGeometricIncrease());
    break;
  case Options::SatRestartStrategy::LUBY:
    _restartStrategy = new LubyRestartStrategy(opt.satRestartLubyFactor());
    break;
  case Options::SatRestartStrategy::MINISAT:
    _restartStrategy = new MinisatRestartStrategy(opt.satRestartMinisatInit(), opt.satRestartMinisatIncrease());
    break;
  }

  switch(opt.satClauseDisposer()) {
  case Options::SatClauseDisposer::GROWING:
    _clauseDisposer = new GrowingClauseDisposer(*this, opt.satVarActivityDecay());
    break;
  case Options::SatClauseDisposer::MINISAT:
    _clauseDisposer = new MinisatClauseDisposer(*this, opt.satVarActivityDecay());
    break;
  }

  _doLearntMinimization = opt.satLearntMinimization();
  _doLearntSubsumptionResolution = opt.satLearntSubsumptionResolution();
}

TWLSolver::~TWLSolver()
{
  while(_learntClauses.isNonEmpty()) {
    SATClause* cl = _learntClauses.pop();
    cl->destroy();
  }
}

/**
 * Make the SAT solver handle SAT clauses with variables
 * from 1 to @b newVarCnt
 */
void TWLSolver::ensureVarCount(unsigned newVarCnt)
{
  CALL("TWLSolver::ensureVarCount");
  
  if(newVarCnt<=_varCnt) {
    return;
  }

  _assignment.expand(newVarCnt+1, AS_UNDEFINED);
  _assignmentLevels.expand(newVarCnt+1);
  _assignmentPremises.expand(newVarCnt+1, 0);
  _lastAssignments.expand(newVarCnt+1, AS_UNDEFINED);
  _propagationScheduled.expand(newVarCnt+1);

  _windex.expand((newVarCnt+1)*2);

  _varCnt=newVarCnt;

  _variableSelector->ensureVarCount(newVarCnt);
}

unsigned TWLSolver::newVar()
{
  CALL("TWLSolver::newVar");
  
  _varCnt++;
  
  _assignment.expand(_varCnt+1, AS_UNDEFINED);
  _assignmentLevels.expand(_varCnt+1);
  _assignmentPremises.expand(_varCnt+1, 0);
  _lastAssignments.expand(_varCnt+1, AS_UNDEFINED);
  _propagationScheduled.expand(_varCnt+1);

  _windex.expand((_varCnt+1)*2);

  _variableSelector->ensureVarCount(_varCnt);
  
  return _varCnt;
}

/**
 * Add a clause into the SAT solver noticing obvious conflicts.
 *
 * The solver will keep the clause (potentially modify it)
 * but it is not responsible for releasing the memory,
 * which is not ideal.
 * (Possible solution: implement reference counting of SATClauses)
 */
void TWLSolver::addClause(SATClause* cl)
{
  CALL("TWLSolver::addClause");
  TimeCounter tc(TC_TWLSOLVER_ADD);
  ASS_EQ(_assumptionCnt, 0);
  ASS(!_unsatisfiableAssumptions);

  LOG2((void*)this," addClauses");

  if(_status==UNSATISFIABLE) {
    return;
  }

  _status = UNKNOWN;
  
  try {
    env.statistics->satTWLClauseCount++;

    ASS(cl->hasUniqueVariables());
    cl->setKept(true);

    LOG1(cl->toString());

    if(cl->length()==0) {
      _status=UNSATISFIABLE;
      _refutation = cl;
    } else if(cl->length()==1) {
      addUnitClause(cl);
    }
    else {
      addNonunitClause(cl);
    }
    _variableSelector->onInputClauseAdded(cl);
    _clauseDisposer->onNewInputClause(cl);
  } catch (const UnsatException& e) {
    _status=UNSATISFIABLE;
    _refutation = e.refutation;
    ASS(!_generateProofs || _refutation);
  }
}

/**
 * This implementation follows the scheme of the original implementation of global subsumption
 *  which relied on the old SAT Solver interface and on TWLSolver as the only SAT solver.
 *
 * TODO: Can we deal with assumptions as minisat does, to naturally discover a nice(ish) subset
 * via the conflict clause learning mechanism?
 */
SATSolver::Status TWLSolver::solveUnderAssumptions(const SATLiteralStack& assumps, unsigned conflictCountLimit, bool onlyProperSubusets)
{
  CALL("TWLSolver::solveUnderAssumptions");

  ASS(!hasAssumptions());

  Status res;
  SATLiteral lit;
  
  // first check the empty set of assumptions
  _failedAssumptionBuffer.reset();
  res = solve(conflictCountLimit);
  if (res == UNSATISFIABLE) {
    return res;
  }
  
  unsigned sz = assumps.size();

  for (unsigned i = 0; i < sz; i++) { // which one to leave out for now
    _failedAssumptionBuffer.reset();
    retractAllAssumptions(); // no-op for the first pass

    for (unsigned j = 0; j < sz; j++) {
      if (i == j) {
        continue;
      }

      lit = assumps[j];
      addAssumption(lit);
      _failedAssumptionBuffer.push(lit);
      res = solve(conflictCountLimit);

      if (res == UNSATISFIABLE) {
        retractAllAssumptions();
        return res;
      }
    }
  }

  if (!onlyProperSubusets) {
    // we must also check with all of them; the last left out was (sz-1)-th
    lit = assumps[sz-1];
    addAssumption(lit);
    _failedAssumptionBuffer.push(lit);
    res = solve(conflictCountLimit);
  } else {
    res = UNKNOWN;
  }

  retractAllAssumptions();
  return res;
}

const SATLiteralStack& TWLSolver::explicitlyMinimizedFailedAssumptions(unsigned conflictCountLimit, bool randomize)
{
  CALL("TWLSolver::explicitlyMinimizedFailedAssumptions");

  // minimize _failedAssumptionBuffer using parent's code:
  SATSolverWithAssumptions::explicitlyMinimizedFailedAssumptions(conflictCountLimit, randomize);

  // the following is only necessary, because during explicit minimization calls to solve may invalidate _refutation
  // TODO: a better solution?

  unsigned sz = _failedAssumptionBuffer.size();
  for (unsigned i = 0; i < sz; i++) {
    addAssumption(_failedAssumptionBuffer[i]);
  }
  ALWAYS(solve(conflictCountLimit) == UNSATISFIABLE);
  retractAllAssumptions();

  return _failedAssumptionBuffer;
}


/**
 * Perform saturation for @c conflictCountLimit conflicts.
 *
 * If concrete status is not established by then, return UNKNOWN.
 */
SATSolver::Status TWLSolver::solve(unsigned conflictCountLimit) {
  CALL("TWLSolver::solve(unsigned)");
  
  if(_status==UNSATISFIABLE) {
    return UNSATISFIABLE;
  }
  
  try {
    env.statistics->satTWLSATCalls++;
    doSolving(conflictCountLimit);  // sets _status to SAT or raises
  } catch (const UnsatException& e) {     
    _status=UNSATISFIABLE;
    _refutation = e.refutation;
    ASS(!_generateProofs || _refutation);
    if(_assumptionsAdded){ _unsatisfiableAssumptions=true;}
  }
  
  LOG3((void*)this," solve ",_status);

  return _status;
}


void TWLSolver::addAssumption(SATLiteral lit)
{
  CALL("TWLSolver::addAssumption");
  _assumptionsAdded = true;

  LOG2("addAssumption ",lit);

  if(_status==UNSATISFIABLE) {
    return;
  }

  try
  {
    backtrack(1);
    doBaseLevelPropagation(); // this is to make sure we have fully propagated (after previous addClause and addAssumption calls)

    if(isFalse(lit)) {
      handleConflictingAssumption(lit);
      ASSERTION_VIOLATION; //exception must be thrown in handleConflictingAssumption()
    }
    if(isTrue(lit)) {
      //the assumption follows from unit propagation
      return;
    }
    makeAssumptionAssignment(lit);  //increases _assumptionCnt
  } catch (const UnsatException& e)
  {
    _unsatisfiableAssumptions = true;
    _status = UNSATISFIABLE;
    _refutation = e.refutation;
    ASS(!_generateProofs || _refutation);
  }
}

void TWLSolver::retractAllAssumptions()
{
  CALL("TWLSolver::retractAllAssumptions");
  _assumptionsAdded = false;

  LOG1("retractAllAssumptions");

  if(_unsatisfiableAssumptions) {
    _status = UNKNOWN;
    _unsatisfiableAssumptions = false;
  }

  if(_assumptionCnt==0) {
    return;
  }

  backtrack(1);

  while(_assumptionCnt>0) {
    ASS(_unitStack.isNonEmpty());
    USRec rec = _unitStack.pop();
    ASS(!rec.choice); //we're at level 1 where no choice points are
    undoAssignment(rec.var);
    if(rec.assumption) {
      _assumptionCnt--;
    }
  }

  //There wasn't anything to propagate before the first assumption was
  //made, so now we may reset the propagation queue and not miss anything
  //important.
  resetPropagation();
}

/**
 * Record the source of a SATLiteral (for niceness computation)
 * @author Giles
 */
void TWLSolver::recordSource(unsigned satlit, Literal* lit){
  _variableSelector->recordSource(satlit,lit);
}

/**
 * Perform solving with given conflictNumberLimit (or UINT_MAX for unlimited).
 * Update status for SATISFIABLE or UNKNOWN results. The UNSATISFIABLE result
 * passed to caller as a thrown UnsatException.
 */
void TWLSolver::doSolving(unsigned conflictNumberLimit)
{
  CALL("TWLSolver::doSolving");

  if(conflictNumberLimit!=0) {
    SatLoopResult slRes = runSatLoop(conflictNumberLimit);
    if(slRes==SLR_SATISFIABLE) {
      _status = SATISFIABLE;
      return;
    }
  }
  backtrack(1);
  doBaseLevelPropagation();
  _status = UNKNOWN;
}

/**
 * Backtrack at least to level @c tgtLev
 */
void TWLSolver::backtrack(unsigned tgtLevel)
{
  CALL("TWLSolver::backtrack");
  ASS_G(tgtLevel,0);

  if(tgtLevel==_level) {
    return;
  }
  ASSERT_VALID(*this);

  resetPropagation();

  USRec rec;
  for(;;) {
    rec=_unitStack.pop();
    ASS_EQ(rec.choice, (_assignmentPremises[rec.var])==0);
    if(!isUndefined(rec.var)) {
      undoAssignment(rec.var);
    }
    if(rec.choice) {
      _level--;
      ASS_GE(_level, tgtLevel);
      if(_level==tgtLevel) {
	break;
      }
    }
  }

  ASS_EQ(_level, tgtLevel);

#if VDEBUG
  assertValid();
#endif
}

/**
 * Get two highest assignment levels of an non-unit clause
 * (these levels can also be equal).
 */
void TWLSolver::getTwoHighestAssignmentLevels(SATClause* cl, unsigned& highestAL, unsigned& secondHighestAL)
{
  CALL("TWLSolver::getTwoHighestAssignmentLevels");
  ASS_G(cl->length(),1);
  ASSERT_VALID(*this);

  highestAL = 1;
  secondHighestAL = 1;

  SATClause::Iterator ccit(*cl);
  while(ccit.hasNext()) {
    SATLiteral lit = ccit.next();
    ASS(isFalse(lit));
    unsigned varAL = getAssignmentLevel(lit);
    if(varAL>highestAL) {
      secondHighestAL = highestAL;
      highestAL = varAL;
    }
    else if(varAL>secondHighestAL) {
      secondHighestAL = varAL;
    }
  }
  ASS_GE(highestAL, secondHighestAL);
}

/**
 * If @c conflictClause can be used for unit propagation,
 * return the lowest level where @c learntClause can be done. Otherwise return
 * the highest level where the clause is valid.
 */
unsigned TWLSolver::getBacktrackLevel(SATClause* conflictClause)
{
  CALL("TWLSolver::getBacktrackLevel");
  ASS_G(conflictClause->length(),1);

  unsigned al1, al2;
  getTwoHighestAssignmentLevels(conflictClause, al1, al2);
  if(al1==al2) {
    return al1-1;
  }
  return al2;
}

/**
 * Return the lowest level where @c learntClause can be used for unit propagation
 */
unsigned TWLSolver::getLearntBacktrackLevel(SATClause* learntClause)
{
  CALL("TWLSolver::getLearntBacktrackLevel");
  ASS_G(learntClause->length(),1);

  unsigned al1, al2;
  getTwoHighestAssignmentLevels(learntClause, al1, al2);
  if(al1==al2) {
    ASS_EQ(al1,1);
    return 0;
  }
  ASS_G(al1,al2);
  return al2;
}

void TWLSolver::doSubsumptionResolution(SATLiteralStack& lits, SATClauseList*& premises)
{
  CALL("TWLSolver::doSubsumptionResolution");

  static ArraySet litSet;
  litSet.ensure((_varCnt+1)*2);
  litSet.reset();

  SATLiteralStack::Iterator litScanIt(lits);
  while(litScanIt.hasNext()) {
    SATLiteral lit = litScanIt.next();
    litSet.insert(lit.content());
  }

  SATLiteralStack::Iterator litIt(lits);
  while(litIt.hasNext()) {
    SATLiteral rLit = litIt.next();
    SATLiteral rLitOp = rLit.opposite();

    bool resolved = false;
    SATClause* resolvingClause = 0;
    WatchStack::Iterator wit(getWatchStack(rLitOp));
    while(wit.hasNext()) {
      SATClause* cl = wit.next().cl;
      if(cl->size()!=2) {
	continue;
      }
      SATLiteral other = ((*cl)[0]==rLitOp) ? (*cl)[1] : (*cl)[0];
      ASS(other!=rLit);
      ASS(other!=rLitOp);
      ASS((*cl)[0]==rLitOp || (*cl)[1]==rLitOp);
      if(litSet.find(other.content())) {
	resolvingClause = cl;
	resolved = true;
	break;
      }
    }
    if(resolved) {
      litSet.remove(rLit.content());
      litIt.del();
      if(_generateProofs) {
	SATClauseList::push(resolvingClause, premises);
      }
    }
  }
}

void TWLSolver::doShallowMinimize(SATLiteralStack& lits, ArraySet& seenVars)
{
  CALL("TWLSolver::doShallowMinimize");

  NOT_IMPLEMENTED;//need to implement proof tracking

  SATLiteralStack::Iterator rit(lits);
  while(rit.hasNext()) {
    SATLiteral resLit = rit.next();
    unsigned resLitVar = resLit.var();
    SATClause* prem = _assignmentPremises[resLitVar];
    if(!prem) {
	continue;
    }
    bool redundant = true;
    SATClause::Iterator premLitIt(*prem);
    while(premLitIt.hasNext()) {
      SATLiteral premLit = premLitIt.next();
      if(!seenVars.find(premLit.var()) && (getAssignmentLevel(premLit)>1 || !_assignmentPremises[premLit.var()])) {
	redundant = false;
	break;
      }
    }
    if(redundant) {
      rit.del();
    }
  }
}

void TWLSolver::doDeepMinimize(SATLiteralStack& lits, ArraySet& seenVars, SATClauseList*& premises)
{
  CALL("TWLSolver::doDeepMinimize");

  SATLiteralStack::Iterator rit(lits);
  while(rit.hasNext()) {
    SATLiteral resLit = rit.next();
    if(isRedundant(resLit, seenVars, premises)) {
      rit.del();
    }
  }
}

bool TWLSolver::isRedundant(SATLiteral lit, ArraySet& seenVars, SATClauseList*& premises)
{
  CALL("TWLSolver::isRedundant");

  static ArraySet varsSeenHere;
  varsSeenHere.ensure(_varCnt+1);
  varsSeenHere.reset();
  static Stack<unsigned> toDo;
  toDo.reset();

  SATClauseList* redundancyPremises = 0;

  unsigned litVar = lit.var();

  toDo.push(litVar);

  while(toDo.isNonEmpty()) {
    unsigned clVar = toDo.pop();
    if(varsSeenHere.find(clVar)) {
      continue;
    }
    varsSeenHere.insert(clVar);
    SATClause* cl = _assignmentPremises[clVar];
    if(!cl) {
      if(redundancyPremises) {
	redundancyPremises->destroy();
      }
      return false;
    }
    if(_generateProofs) {
      SATClauseList::push(cl, redundancyPremises);
    }
    SATClause::Iterator premLitIt(*cl);
    while(premLitIt.hasNext()) {
      SATLiteral premLit = premLitIt.next();
      unsigned premVar = premLit.var();
      if(premVar==clVar || seenVars.find(premVar)) {
	continue;
      }
      toDo.push(premVar);
    }
  }
  
  premises = SATClauseList::concat(redundancyPremises, premises);
  return true;
}

SATClause* TWLSolver::getLearntClause(SATClause* conflictClause)
{
  CALL("TWLSolver::getLearntClause");
  ASS(isFalse(conflictClause));

  //variables implied by the current conflict
  //The learnt clause must contradict assignment
  //to at least one of these variables.
  static ArraySet seenVars;
  seenVars.ensure(_varCnt+1);
  seenVars.reset();

  static SATLiteralStack resLits;
  static SATClauseStack toDo;
  SATClauseList* premises = 0;
  resLits.reset();
  toDo.reset();

  toDo.push(conflictClause);
  while(toDo.isNonEmpty()) {
    SATClause* cl=toDo.pop();
    if(_generateProofs) {
      SATClauseList::push(cl, premises);
    }
    recordClauseActivity(cl);
    SATClause::Iterator cit(*cl);
    while(cit.hasNext()) {
      SATLiteral curLit = cit.next();
      unsigned curVar = curLit.var();
      if(seenVars.find(curVar)) {
	continue;
      }
      ASS(isFalse(curLit));
      seenVars.insert(curVar);

      _variableSelector->onVariableInConflict(curVar);

      SATClause* prem = _assignmentPremises[curVar];
      unsigned curLevel = getAssignmentLevel(curLit);
      bool shouldExpand = prem!=0 && curLevel==_level;
      if(shouldExpand) {
	toDo.push(prem);
      }
      else {
	resLits.push(curLit);
      }
    }
  }

//  doShallowMinimize(resLits, seenVars);
  if(_doLearntMinimization) {
    doDeepMinimize(resLits, seenVars, premises);
  }
  if(_doLearntSubsumptionResolution) {
    doSubsumptionResolution(resLits, premises);
  }

  SATClause* res = SATClause::fromStack(resLits);

  if(_generateProofs) {
    ASS(premises);
    SATInference* inf = new PropInference(premises);
    res->setInference(inf);
  }

#if VDEBUG
  if(_level!=1) {
    //we check that there is at most one literal on the current decision level
    bool curLevFound = false;
    SATLiteralStack::Iterator rlIt(resLits);
    while(rlIt.hasNext()) {
      SATLiteral lit = rlIt.next();
      if(getAssignmentLevel(lit)==_level) {
	if(curLevFound) {
	  cout<<"cur lev: "<<_level<<endl;
	  printAssignment();
	}
	ASS(!curLevFound);
	curLevFound = true;
      }
    }
  }
#endif

  ASS(isFalse(res));
  _learntClauses.push(res);
  env.statistics->learntSatClauses++;
  env.statistics->learntSatLiterals += res->length();
//  cout<<res->toString()<<endl;
  recordClauseActivity(res);
  return res;
}

TWLSolver::ClauseVisitResult TWLSolver::visitWatchedClause(Watch watch, unsigned var, unsigned& litIndex)
{
  CALL("TWLSolver::visitWatchedClause");

  ASS_G(var,0); ASS_LE(var,_varCnt);

  if(isTrue(watch.blocker)) {
    return VR_NONE;
  }

  SATClause* cl = watch.cl;

  unsigned curWatchIndex=
      ((*cl)[0].var()==var) ? 0 : 1;
  ASS_EQ((*cl)[curWatchIndex].var(), var);
  ASS(isFalse((*cl)[curWatchIndex]));

  unsigned otherWatchIndex=1-curWatchIndex;

  const SATLiteral& otherWatched = (*cl)[otherWatchIndex];
  ASS_NEQ((*cl)[otherWatchIndex].var(), var);

  if(watch.blocker!=otherWatched && isTrue(otherWatched)) {
//  if(isTrue(otherWatched)) {
    return VR_NONE; //the other watched literal is true
  }
  ASS(!isTrue(otherWatched));

  unsigned clen=cl->length();
  unsigned undefIndex=clen; //contains the first undefined non-watched literal or clen if there is none

  for(unsigned i=2;i<clen;i++) { //we start from the first non-watched literal (which is at position 2)
    SATLiteral lit=(*cl)[i];
    if(isTrue(lit)) {
      //clause is true
      return VR_NONE;
    }
    else if(undefIndex==clen && isUndefined(lit)) {
      undefIndex=i;
    }
  }

  //  if(undefIndex!=clen && isUndefined((*cl)[otherWatchIndex])) {
  if(undefIndex!=clen) {
    //The other watched literal is undefined and there is also another undefined literal.
    //So we just replace the current watched by the other undefined.
    litIndex = undefIndex;
    return VR_CHANGE_WATCH;
  }

  if(!isUndefined(otherWatched)) {
    //there is no undefined literal, so the whole clause is false
    ASS_REP(isFalse(cl), *cl);
    return VR_CONFLICT;
  }

  //Here we know that exactly one literal (the other watched one) is undefined and all others are false.
  litIndex = otherWatchIndex;
  return VR_PROPAGATE;
}

/**
 * Perform unit propagation starting with variable @c var0.
 *
 * If conflict occurs, return the clause that caused the conflict;
 * otherwise return 0.
 */
SATClause* TWLSolver::propagate(unsigned var)
{
  CALL("TWLSolver::propagate");
  ASS_G(var,0); ASS_LE(var,_varCnt);
  ASS(!isUndefined(var));

  //we go through the watch stack of literal opposite to the assigned value
//  WatchStack::Iterator wit(getTriggeredWatchStack(var, _assignment[var]));
  WatchStack::StableDelIterator wit(getTriggeredWatchStack(var, _assignment[var]));
  while(wit.hasNext()) {
    Watch watch=wit.next();
    SATClause* cl = watch.cl;

    unsigned litIndex;
    ClauseVisitResult cvr = visitWatchedClause(watch, var, litIndex);
    switch(cvr) {
    case VR_CHANGE_WATCH:
    {
      WatchStack& tgtStack = getWatchStack((*cl)[litIndex]);
      unsigned curWatchIndex = ((*cl)[0].var()==var) ? 0 : 1;
      swap( (*cl)[curWatchIndex], (*cl)[litIndex] );
      wit.del();
      tgtStack.push(Watch(cl, (*cl)[1-curWatchIndex]));
      break;
    }
    case VR_CONFLICT:
      return cl;
    case VR_PROPAGATE:
    {
      //So let's unit-propagate...
      SATLiteral undefLit=(*cl)[litIndex];
      makeForcedAssignment(undefLit, cl);
      break;
    }
    case VR_NONE:
      break;
    }
  }
  return 0;
}

void TWLSolver::setAssignment(unsigned var, unsigned polarity)
{
  CALL("TWLSolver::setAssignment");
  ASS_G(var,0); ASS_LE(var,_varCnt);

  _assignment[var] = static_cast<AsgnVal>(polarity);
  _lastAssignments[var] = static_cast<AsgnVal>(polarity);
}

void TWLSolver::makeAssumptionAssignment(SATLiteral lit)
{
  CALL("TWLSolver::makeAssumptionAssignment");
  ASS_EQ(_level, 1);

  unsigned var = lit.var();
  ASS(isUndefined(var));

  _assumptionCnt++;
  setAssignment(var, lit.polarity());
  _assignmentLevels[var]=1;
  _assignmentPremises[var]=0;
  _unitStack.push(USRec(var, false, true));
  schedulePropagation(var);
}

void TWLSolver::makeChoiceAssignment(unsigned var, unsigned polarity)
{
  CALL("TWLSolver::makeChoiceAssignment");
  ASS_G(var,0); ASS_LE(var,_varCnt);

  _level++;

  ASS(isUndefined(var));
  setAssignment(var, polarity);
  _assignmentLevels[var]=_level;
  _assignmentPremises[var]=0;
  _unitStack.push(USRec(var, true));
  schedulePropagation(var);
}

void TWLSolver::makeForcedAssignment(SATLiteral lit, SATClause* premise)
{
  CALL("TWLSolver::makeForcedAssignment");

  unsigned var = lit.var();

  ASS(isUndefined(var));
  setAssignment(var, lit.polarity());
  _assignmentLevels[var]=_level;
  _assignmentPremises[var]=premise;
  _unitStack.push(USRec(var, false));
  schedulePropagation(var);
}

void TWLSolver::undoAssignment(unsigned var)
{
  CALL("TWLSolver::undoAssignment");
  ASS_G(var,0); ASS_LE(var,_varCnt);

  _assignment[var] = AS_UNDEFINED;
  _assignmentPremises[var] = 0;

  _variableSelector->onVariableUnassigned(var);
}

void TWLSolver::addUnitClause(SATClause* cl)
{
  CALL("TWLSolver::addUnitClause");

  SATLiteral lit=(*cl)[0];

  backtrack(1);
  if(isFalse(lit)) {
    handleTopLevelConflict(cl);
  }
  if(isUndefined(lit)) {
    makeForcedAssignment(lit, cl);
  }
}

void TWLSolver::handleTopLevelConflict(SATClause* cl)
{
  CALL("TWLSolver::handleTopLevelConflict");

  if(_level!=1) {
    backtrack(1);
  }
  ASS(isFalse(cl));

  SATClause* refutation = 0;
  if(_generateProofs) {
    refutation = getLearntClause(cl);
  }
  throw UnsatException(refutation);
}

void TWLSolver::handleConflictingAssumption(SATLiteral assumpt)
{
  CALL("TWLSolver::handleConflictingAssumption");
  ASS_EQ(_level, 1);
  ASS(isFalse(assumpt));

  if(!_generateProofs) {
    throw UnsatException();
  }
  static SATLiteralStack litStack;
  litStack.reset();
  litStack.push(assumpt);
  SATClause* confl = SATClause::fromStack(litStack);
  confl->setInference(new AssumptionInference());

  handleTopLevelConflict(confl);
}

/**
 * Select two best literals in @c cl and return number of non-false
 * ones among selected.
 * Best literals are those that are not false (i.e. are true or undefined).
 * Among false literals are better those from higher assignment levels.
 */
unsigned TWLSolver::selectTwoNonFalseLiterals(SATClause* cl) const
{
  CALL("TWLSolver::selectTwoNonFalseLiterals");

  unsigned clen=cl->length();
  ASS_G(clen,1);

  unsigned wCnt=0;
  for(unsigned i=0;i<clen;i++) {
    SATLiteral lit=(*cl)[i];
    if(!isFalse(lit)) {
      //literal is either true or undefined
      swap( (*cl)[wCnt], (*cl)[i] );
      wCnt++;
      if(wCnt==2) {
	break;
      }
    }
  }
  if(wCnt==2) {
    return 2;
  }
  if(wCnt==1) {
    unsigned hLevIndex=1;
    unsigned hLev=getAssignmentLevel((*cl)[1]);

    for(unsigned i=2;i<clen;i++) {
      unsigned curLev=getAssignmentLevel((*cl)[i]);
      if(curLev > hLev) {
	hLevIndex=i;
	hLev=curLev;
      }
    }
    swap( (*cl)[1], (*cl)[hLevIndex] );
    return 1;
  }
  ASS_EQ(wCnt,0);

  if(getAssignmentLevel((*cl)[0]) < getAssignmentLevel((*cl)[1])) {
    swap( (*cl)[0], (*cl)[1] );
  }
  unsigned llvl=getAssignmentLevel((*cl)[1]); //lower of the two highest levels
  for(unsigned i=2;i<clen;i++) {
    unsigned curLev=getAssignmentLevel((*cl)[i]);
    if(curLev > llvl) {
      swap( (*cl)[1], (*cl)[i] );
      if(getAssignmentLevel((*cl)[0]) < curLev) {
        swap( (*cl)[0], (*cl)[1] );
      }
      llvl=getAssignmentLevel((*cl)[1]);
    }
  }
  return 0;
}

void TWLSolver::addNonunitClause(SATClause* cl)
{
  CALL("TWLSolver::addNonunitClause");

  ASS_G(cl->length(),1);

  unsigned wCnt=selectTwoNonFalseLiterals(cl);

  if(wCnt==0) {
    //the added clause is false, so we need to backtrack to get some space
    //to fix the assignment

    unsigned btLev=getBacktrackLevel(cl);
    if(btLev==0) {
      handleTopLevelConflict(cl);
    }
    ASS_NEQ(btLev, _level);
    backtrack(btLev);
    ASS(isUndefined((*cl)[0]));

    //we have changed assignments, so we need to bring the undefined and high assigned
    //literals to front
    wCnt = selectTwoNonFalseLiterals(cl);
    ASS_GE(wCnt,1); //at least one literal should be undefined
    ASS(isUndefined((*cl)[0]));
    ASS(wCnt==1 || isUndefined((*cl)[1]));
  }

  if(wCnt==2) {
    //if there are two non-false literals, we can just watch them
    insertIntoWatchIndex(cl);
    return;
  }

  ASS_EQ(wCnt,1);
  SATLiteral wLit=(*cl)[0];
  unsigned hLev=getAssignmentLevel((*cl)[1]);

  if(hLev!=_level) {
    ASS_L(hLev,_level);
    backtrack(hLev);
  }

  if(isTrue(wLit)) {
    insertIntoWatchIndex(cl);
  }
  else {
    ASS(isUndefined(wLit));
    makeForcedAssignment(wLit, cl);
    insertIntoWatchIndex(cl);
  }
}


void TWLSolver::schedulePropagation(unsigned var)
{
  CALL("TWLSolver::schedulePropagation");

  ASS_G(var,0); ASS_LE(var,_varCnt);

  if(_propagationScheduled.find(var)) {
    return;
  }
  _propagationScheduled.insert(var);
  _toPropagate.push_back(var);
}

void TWLSolver::resetPropagation()
{
  CALL("TWLSolver::resetPropagation");

  if(_toPropagate.isEmpty()) {
    return;
  }

  _propagationScheduled.reset();
  _toPropagate.reset();
}

unsigned TWLSolver::pickForPropagation()
{
  CALL("TWLSolver::pickForPropagation");
  ASS(_toPropagate.isNonEmpty());

  unsigned var;
//  var = _toPropagate.pop_back();
  var = _toPropagate.pop_front();
  _propagationScheduled.remove(var);
  return var;
}

void TWLSolver::recordClauseActivity(SATClause* cl)
{
  CALL("TWLSolver::recordClauseActivity");

  _clauseDisposer->onClauseInConflict(cl);
}

/**
 * Make the first two literals of clause @c cl watched.
 */
void TWLSolver::insertIntoWatchIndex(SATClause* cl)
{
  CALL("TWLSolver::insertIntoWatchIndex");

  getWatchStack((*cl)[0]).push(Watch(cl, (*cl)[1]));
  getWatchStack((*cl)[1]).push(Watch(cl, (*cl)[0]));
}

void TWLSolver::assertValid()
{
  CALL("TWLSolver::assertValid");

  for(unsigned i=1;i<=_varCnt;i++) {
    if(_assignment[i]!=AS_UNDEFINED) {
      ASS_LE(getAssignmentLevel(i),_level);
    }
  }

  Stack<USRec>::Iterator uit(_unitStack);
  while(uit.hasNext()) {
    USRec rec=uit.next();
    ASS_NEQ(_assignment[rec.var], AS_UNDEFINED);
  }
}

inline WatchStack& TWLSolver::getWatchStack(SATLiteral lit)
{
  CALL("TWLSolver::getWatchStack/1");

  return _windex[lit.content()];
}

inline WatchStack& TWLSolver::getWatchStack(unsigned var, unsigned polarity)
{
  CALL("TWLSolver::getWatchStack/2");
  ASS_G(var,0); ASS_LE(var,_varCnt);
  ASS_REP(polarity==0 || polarity==1, polarity);

  return _windex[2*var + polarity];
}

inline WatchStack& TWLSolver::getTriggeredWatchStack(unsigned var, PackedAsgnVal assignment)
{
  CALL("TWLSolver::getTriggeredWatchStack");
  ASS_G(var,0); ASS_LE(var,_varCnt);
  ASS(assignment!=AS_UNDEFINED);

  return getWatchStack(var, 1-assignment);
}


/** Return true iff @c lit is true in the current assignment */
inline bool TWLSolver::isTrue(const SATLiteral& lit) const
{
  CALL("TWLSolver::isTrue");

  return _assignment[lit.var()] == static_cast<AsgnVal>(lit.polarity());
}

/** Return true iff @c lit is false in the current assignment */
inline bool TWLSolver::isFalse(const SATLiteral& lit) const
{
  CALL("TWLSolver::isFalse");

  return _assignment[lit.var()] == static_cast<AsgnVal>(lit.oppositePolarity());
}

/** Return true iff @c lit is undefined in the current assignment */
inline bool TWLSolver::isUndefined(const SATLiteral& lit) const
{
  CALL("TWLSolver::isUndefined(SATLiteral)");

  return isUndefined(lit.var());
}

/**
 * Return level on which was literal @c lit assigned.
 *
 * Literal @c lit cannot be undefined.
 */
inline unsigned TWLSolver::getAssignmentLevel(SATLiteral lit) const
{
  CALL("TWLSolver::getAssignmentLevel(SATLiteral)");

  return getAssignmentLevel(lit.var());
}

/**
 * Return level on which was variable @c var assigned.
 *
 * Variable @c var cannot be undefined.
 */
inline unsigned TWLSolver::getAssignmentLevel(unsigned var) const
{
  CALL("TWLSolver::getAssignmentLevel(unsigned)");
  ASS_G(var,0); ASS_LE(var,_varCnt);
  ASS(!isUndefined(var));

  return _assignmentLevels[var];
}

/** Return true iff all literals in @c c are false in the current assignment */
bool TWLSolver::isFalse(SATClause* cl) const
{
  CALL("TWLSolver::isFalse");

  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++) {
    if( !isFalse((*cl)[i]) ) {
      return false;
    }
  }
  return true;
}

bool TWLSolver::isTrue(SATClause* cl) const
{
  CALL("TWLSolver::isTrue");

  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++) {
    if( isTrue((*cl)[i]) ) {
      return true;
    }
  }
  return false;
}

SATSolver::VarAssignment TWLSolver::getAssignment(unsigned var)
{
  CALL("TWLSolver::getAssignment");
  ASS_G(var,0); ASS_LE(var,_varCnt);
  ASS(_status == SATISFIABLE || _status == UNKNOWN);
          
  if(isTrue(var)) {
    return SATSolver::TRUE;
  }
  else if(isUndefined(var)) {
     /* This can happen when there has been a request for new variables
      * after the SATISFIABLE status has been established.
    */
    return SATSolver::DONT_CARE;
  }
  else {
    return SATSolver::FALSE;
  }
}

bool TWLSolver::isZeroImplied(unsigned var)
{
  CALL("TWLSolver::isZeroImplied");
  ASS_G(var,0); ASS_LE(var,_varCnt);

  return !isUndefined(var) && (getAssignmentLevel(var)==1);
}

void TWLSolver::collectZeroImplied(SATLiteralStack& acc)
{
  CALL("TWLSolver::collectZeroImplied");
  ASS_NEQ(_status,UNSATISFIABLE);

  Stack<USRec>::BottomFirstIterator usit(_unitStack);
  while(usit.hasNext()) {
    const USRec& usr = usit.next();
    if(usr.choice) {
      return;
    }
    unsigned var = usr.var;
    ASS_EQ(getAssignmentLevel(var),1);
    bool pol = isTrue(var);
    SATLiteral lit(var, pol);
    ASS(isTrue(lit));
    acc.push(lit);
  }
}

/**
 * Return a valid clause that contains the zero-implied literal
 * and possibly the assumptions that implied it. Return 0 if @c var
 * was an assumption itself.
 * If called on a proof producing solver, the clause will have
 * a proper proof history.
 */
SATClause* TWLSolver::getZeroImpliedCertificate(unsigned var)
{
  CALL("TWLSolver::getZeroImpliedCertificate");
  ASS_G(var,0); ASS_LE(var,_varCnt);
  ASS(isZeroImplied(var));
  ASS_EQ(getAssignmentLevel(var),1);

  if(_assignmentPremises[var]==0) {
    //variable itself is an assumption
    return 0;
  }


  static ArraySet seen;
  seen.ensure(_varCnt+1);
  seen.reset();
  static Stack<unsigned> toDo;
  toDo.reset();
  static SATClauseStack prems;
  static SATLiteralStack resLits;
  resLits.reset();

  seen.insert(var);
  resLits.push(SATLiteral(var, _assignment[var])); //assignment values, even though ternary, translate well to boolean polarity

  SATClause* prem = _assignmentPremises[var];
  for(;;) {
    prems.push(prem);
    SATClause::Iterator pit(*prem);
    while(pit.hasNext()) {
      SATLiteral pl = pit.next();
      unsigned pvar = pl.var();
      if(seen.find(pvar)) {
	continue;
      }
      seen.insert(pvar);
      toDo.push(pvar);
    }

    while(toDo.isNonEmpty() && !_assignmentPremises[toDo.top()]) {
      //we have an assumption
      unsigned currVar = toDo.pop();
      ASS_NEQ(_assignment[currVar],AS_UNDEFINED);
      ASS_EQ(getAssignmentLevel(currVar),1);
      resLits.push(SATLiteral(currVar, !_assignment[currVar])); //we add negations of assumed literals
    }
    if(toDo.isEmpty()) {
      break;
    }
    unsigned currVar = toDo.pop();
    prem = _assignmentPremises[currVar];
    ASS(prem);
  }

  SATClause* res = SATClause::fromStack(resLits);
  if(_generateProofs) {
    SATClauseList* premLst = 0;
    SATClauseList::pushFromIterator(SATClauseStack::Iterator(prems), premLst);
    SATInference* inf = new PropInference(premLst);
    res->setInference(inf);
  }
  return res;
}

void TWLSolver::printAssignment()
{
  CALL("TWLSolver::printAssignment");

  for(unsigned i=1;i<=_varCnt;i++) {
    if(_assignment[i]==AS_UNDEFINED) {
      cout<<i<<"\t"<<static_cast<AsgnVal>(_assignment[i])<<endl;
    } else {
      cout<<i<<"\t"<<static_cast<AsgnVal>(_assignment[i])<<"\t"<<getAssignmentLevel(i);
      if(_assignmentPremises[i]) {
	cout<<"\t"<<(*_assignmentPremises[i])<<"\t"<<_assignmentPremises[i];
      }
      cout<<endl;
    }
  }
}

void TWLSolver::doBaseLevelPropagation()
{
  CALL("TWLSolver::doBaseLevelPropagation");
  ASS_EQ(_level, 1);

  while(anythingToPropagate()) {
    unsigned propagatedVar = pickForPropagation();
    SATClause* conflict = propagate(propagatedVar);
    if(conflict) {
      handleTopLevelConflict(conflict);
    }
  }
}

TWLSolver::SatLoopResult TWLSolver::runSatLoop(unsigned conflictCountLimit)
{
  CALL("TWLSolver::runSatLoop");

  SatLoopResult res = SLR_UNKNOWN;

  _restartStrategy->reset();

  size_t conflictsBeforeRestart = _restartStrategy->getNextConflictCount();
  bool conflictCountLimited = conflictCountLimit!=UINT_MAX;
  unsigned conflictCountLimitRemaining = conflictCountLimit;
  bool restartASAP = false;

  for(;;) {

    if(restartASAP) {
      backtrack(1);
      _variableSelector->onRestart();
      _clauseDisposer->onRestart();
      conflictsBeforeRestart = _restartStrategy->getNextConflictCount();
      restartASAP = false;
    }

    if(_toPropagate.isEmpty()) {
      _clauseDisposer->onSafeSpot();
    }

    if(!anythingToPropagate()) {
      if(conflictCountLimitRemaining==0) {
	res = SLR_CONFLICT_LIMIT_REACHED;
	break;
      }
      unsigned choiceVar;
      if(!_variableSelector->selectVariable(choiceVar)) {
        //We don't havething to propagate, nor any choice points. This means
        //we have fount an assignment.
	res = SLR_SATISFIABLE;
	break;
      }
      PackedAsgnVal asgn = _lastAssignments[choiceVar];
      if(asgn==AS_UNDEFINED) {
//	asgn = (getWatchStack(choiceVar, 0).size()>getWatchStack(choiceVar, 1).size()) ? AS_FALSE : AS_TRUE;
	asgn = (getWatchStack(choiceVar, 0).size()>getWatchStack(choiceVar, 1).size()) ? AS_TRUE : AS_FALSE;
      }
      makeChoiceAssignment(choiceVar, asgn);
    }
    unsigned propagatedVar = pickForPropagation();
    env.checkTimeSometime<500>();

    SATClause* conflict = propagate(propagatedVar);
    while(conflict) {
      ASS_REP(isFalse(conflict),conflict);
      if(conflictsBeforeRestart==0) {
	restartASAP = true;
      }
      else {
	conflictsBeforeRestart--;
      }
      if(conflictCountLimited && conflictCountLimitRemaining!=0) {
	conflictCountLimitRemaining--;
      }
      _variableSelector->onConflict();
      _clauseDisposer->onConflict();
      SATClause* learnt = getLearntClause(conflict);
      ASS_REP(isFalse(learnt),learnt);

      if(learnt->length()==0) {
	throw UnsatException(learnt);
      }
      if(learnt->length()==1) {
	SATLiteral lit = (*learnt)[0];
	unsigned lvar = lit.var();
	backtrack(1);
	if(isFalse(lit)) {
	  handleTopLevelConflict(learnt);
	}
	ASS(isUndefined(lit));
	makeForcedAssignment(lit, learnt);
	conflict = propagate(lvar);
	continue;
      }

      unsigned nonFalseLitCnt;
      do {
	unsigned propBtLev = getLearntBacktrackLevel(learnt);
	if(propBtLev==0) {
	  handleTopLevelConflict(learnt);
	}
	backtrack(propBtLev);
	nonFalseLitCnt = selectTwoNonFalseLiterals(learnt);
      } while(nonFalseLitCnt==0);

      insertIntoWatchIndex(learnt);
      if(nonFalseLitCnt==1) {
	ASS(isFalse((*learnt)[1]));
	unsigned propagatedVar = (*learnt)[1].var();
	conflict = propagate(propagatedVar);
      }
      else {
	ASS_EQ(nonFalseLitCnt,2);
	conflict = 0;
      }
    }
  }
  ASS_NEQ(res,SLR_UNKNOWN);
  return res;
}

}
