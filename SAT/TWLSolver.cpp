/**
 * @file TWLSolver.cpp
 * Implements class TWLSolver.
 */


#include "Debug/Assertion.hpp"

#include "Lib/Array.hpp"
#include "Lib/ArrayMap.hpp"
#include "Lib/BinaryHeap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "SATLiteral.hpp"
#include "SATClause.hpp"

#include "RestartStrategy.hpp"
#include "VariableSelector.hpp"
#include "ClauseDisposer.hpp"

#include "TWLSolver.hpp"

#undef LOGGING
#define LOGGING 0

namespace SAT
{

using namespace Lib;

TWLSolver::TWLSolver(const Options& opt, bool generateProofs)
: _opt(opt), _generateProofs(generateProofs), _status(SATISFIABLE), _assignment(0), _assignmentLevels(0),
_windex(0), _varCnt(0), _level(1), _assumptionsAdded(false), _assumptionCnt(0), _unsatisfiableAssumptions(false)
{
  switch(opt.satVarSelector()) {
  case Options::SVS_ACTIVE:
    _variableSelector = new ActiveVariableSelector(*this, opt.satVarActivityDecay());
    break;
  case Options::SVS_RECENTLY_LEARNT:
    _variableSelector = new RLCVariableSelector(*this);
    break;
  }

//  _variableSelector = new AlternatingVariableSelector(*this, new ActiveVariableSelector(*this), new ArrayActiveVariableSelector(*this));


  switch(opt.satRestartStrategy()) {
  case Options::SRS_FIXED:
    _restartStrategy = new FixedRestartStrategy(opt.satRestartFixedCount());
    break;
  case Options::SRS_GEOMETRIC:
    _restartStrategy = new GeometricRestartStrategy(opt.satRestartGeometricInit(), opt.satRestartGeometricIncrease());
    break;
  case Options::SRS_LUBY:
    _restartStrategy = new LubyRestartStrategy(opt.satRestartLubyFactor());
    break;
  case Options::SRS_MINISAT:
    _restartStrategy = new MinisatRestartStrategy(opt.satRestartMinisatInit(), opt.satRestartMinisatIncrease());
    break;
  }

  switch(opt.satClauseDisposer()) {
  case Options::SCD_GROWING:
    _clauseDisposer = new GrowingClauseDisposer(*this, opt.satVarActivityDecay());
    break;
  case Options::SCD_MINISAT:
    _clauseDisposer = new MinisatClauseDisposer(*this, opt.satVarActivityDecay());
    break;
  }
}

TWLSolver::~TWLSolver()
{
  while(_learntClauses.isNonEmpty()) {
    SATClause* cl = _learntClauses.pop();
    cl->destroy();
  }
}

/**
 * Make the SAT solver handle SAT clauses with variables up to
 * @b newVarCnt-1
 */
void TWLSolver::ensureVarCnt(unsigned newVarCnt)
{
  CALL("TWLSolver::ensureVarCnt");

  if(newVarCnt<=_varCnt) {
    return;
  }

  _assignment.expand(newVarCnt, AS_UNDEFINED);
  _assignmentLevels.expand(newVarCnt);
  _assignmentPremises.expand(newVarCnt, 0);
  _lastAssignments.expand(newVarCnt, AS_UNDEFINED);
  _propagationScheduled.expand(newVarCnt);

  _windex.expand(newVarCnt*2);

  _varCnt=newVarCnt;

  _variableSelector->ensureVarCnt(newVarCnt);
}

/**
 * Add clauses into the SAT solver and saturate. New clauses cannot
 * be added when there are any non-retracted assumptions.
 *
 * If @c onlyPropagate is true, only unit propagation is done. If
 * unsatisfiability isn't shown in this case, the status is set to UNKNOWN.
 */
void TWLSolver::addClauses(SATClauseIterator cit, bool onlyPropagate)
{
  CALL("TWLSolver::addClauses");
  ASS_EQ(_assumptionCnt, 0);
  ASS(!_unsatisfiableAssumptions);

  LOG("sat","adding clauses"<<(onlyPropagate ? " (only propagate)":""));

  if(_status==UNSATISFIABLE) {
    return;
  }

  try {
    while(cit.hasNext()) {
      SATClause* cl=cit.next();
      LOG("sat_clauses",*cl);
      cl->setKept(true);
      if(cl->length()==1) {
	addUnitClause(cl);
      } else {
	addClause(cl);
      }
      _variableSelector->onInputClauseAdded(cl);
      _clauseDisposer->onNewInputClause(cl);
    }
    if(onlyPropagate) {
      backtrack(1);
      doBaseLevelPropagation();
    }
    else {
      runSatLoop();
    }

  } catch (UnsatException e)
  {
    _status=UNSATISFIABLE;
    _refutation = e.refutation;
    ASS(!_generateProofs || _refutation);
  }
}

void TWLSolver::addAssumption(SATLiteral lit, bool onlyPropagate)
{
  CALL("TWLSolver::addAssumption");

  LOG("sat_asmp","add assumption "<<lit);

  _assumptionsAdded = true;

  if(_status==UNSATISFIABLE) {
    LOG("sat_asmp","assumption ignored due to unsat state");
    return;
  }
  ASS(!anythingToPropagate());

  //Invariant: before adding assumptions the problem must be satisfiable
  ASS_EQ(_status, SATISFIABLE);

  try
  {
    backtrack(1);
    if(isFalse(lit)) {
      LOG("sat_asmp","assumption immediately unsat");
      handleConflictingAssumption(lit);
      ASSERTION_VIOLATION; //exception must be thrown in handleConflictingAssumption()
    }
    if(isTrue(lit)) {
      //the assumption follows from unit propagation
      LOG("sat_asmp","assumption follows from unit prop");
      return;
    }
    makeAssumptionAssignment(lit);  //increases _assumptionCnt
    LOG("sat_asmp","assumption made");
    if(onlyPropagate) {
      doBaseLevelPropagation();
    }
    else {
      runSatLoop();
    }
  } catch (UnsatException e)
  {
    LOG("sat_asmp","assumption unsat");
    _unsatisfiableAssumptions = true;
    _status = UNSATISFIABLE;
    _refutation = e.refutation;
    ASS(!_generateProofs || _refutation);
  }
}

void TWLSolver::retractAllAssumptions()
{
  CALL("TWLSolver::retractAllAssumptions");

  LOG("sat_asmp","retract assumptions");

  _assumptionsAdded = false;

  if(_unsatisfiableAssumptions) {
    //Invariant: before adding assumptions the problem was satisfiable
    _status = SATISFIABLE;
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
      LOG("sat_asmp","assumption "<<rec.var<<" retracted");
    }
  }

  //There wasn't anything to propagate before the first assumption was
  //made, so now we may reset the propagation queue and not miss anything
  //important.
  resetPropagation();
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

  LOG("sat_levels","backtracked to level "<<_level);
#if VDEBUG
  assertValid();
#endif
}

unsigned TWLSolver::getBacktrackLevel(SATClause* conflictClause)
{
  CALL("TWLSolver::getBacktrackLevel");
  ASSERT_VALID(*this);

  unsigned btLev=0;
  static Stack<SATClause*> confCls;
  static DHMap<unsigned,bool,IdentityHash> checked;
  confCls.reset();
  checked.reset();

  confCls.push(conflictClause);

  while(confCls.isNonEmpty()) {
    SATClause* ccl=confCls.pop();
    unsigned cclen=ccl->length();
    for(unsigned i=0; i<cclen; i++) {
      unsigned lvar=(*ccl)[i].var();

      ASS(!isUndefined(lvar));
      if(_assignmentLevels[lvar]<=btLev+1) {
	continue;
      }
      if(!checked.insert(lvar, true)) {
	//we've already visited this variable
	continue;
      }
      SATClause* icl=_assignmentPremises[lvar];
      if(icl) {
	if(icl!=ccl) {
	  confCls.push(icl);
	}
      } else {
	btLev=max(btLev, _assignmentLevels[lvar]-1);
      }
    }
  }
  ASS_L(btLev, _level);
  return btLev;
}

void TWLSolver::doSubsumptionResolution(SATLiteralStack& lits, SATClauseList*& premises)
{
  CALL("TWLSolver::doSubsumptionResolution");

  static ArraySet litSet;
  litSet.ensure(_varCnt*2);
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

  LOG("sat_learnt_gen","checking redundancy of literal "<<lit);

  static ArraySet varsSeenHere;
  varsSeenHere.ensure(_varCnt);
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
      LOG("sat_learnt_gen","non-redundant "<<lit<<" as "<<clVar<<" is without premise");
      return false;
    }
    if(_generateProofs) {
      SATClauseList::push(cl, redundancyPremises);
    }
    LOG("sat_learnt_gen","examining "<<(*cl)<<" -- premise of "<<clVar);
    SATClause::Iterator premLitIt(*cl);
    while(premLitIt.hasNext()) {
      SATLiteral premLit = premLitIt.next();
      unsigned premVar = premLit.var();
      if(premVar==clVar || seenVars.find(premVar)) {
	continue;
      }
      LOG("sat_learnt_gen","variable "<<premVar<< " goes for further examination");
      toDo.push(premVar);
    }
  }
  TRACE("sat_learnt_prems",
      SATClauseList::Iterator pit(redundancyPremises);
      while(pit.hasNext()) {
	tout << "premise: " << (*pit.next()) << endl;
      }
  );

  premises = SATClauseList::concat(redundancyPremises, premises);
  LOG("sat_learnt_gen","redundant "<<lit);
  return true;
}

SATClause* TWLSolver::getLearntClause(SATClause* conflictClause)
{
  CALL("TWLSolver::getLearntClause");
  ASS(isFalse(conflictClause));

  //variables implied by the current conflict
  //The learnt claue must contradict assignment
  //to at least one of these variables.
  static ArraySet seenVars;
  seenVars.ensure(_varCnt);
  seenVars.reset();

  static SATLiteralStack resLits;
  static SATClauseStack toDo;
  SATClauseList* premises = 0;
  resLits.reset();
  toDo.reset();

  LOG("sat_learnt_gen","LC generating started");
  toDo.push(conflictClause);
  while(toDo.isNonEmpty()) {
    SATClause* cl=toDo.pop();
    if(_generateProofs) {
      SATClauseList::push(cl, premises);
    }
    LOG("sat_learnt_prems","premise: "<<(*cl));
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

  LOG("sat_learnt_gen","init lit cnt: "<<resLits.size()<<" prem cnt: "<<premises->length());
//  cout<<resLits.size()<<" ";
//  doShallowMinimize(resLits, seenVars);
  if(_opt.satLearntMinimization()) {
    doDeepMinimize(resLits, seenVars, premises);
    LOG("sat_learnt_gen","post minimization lit cnt: "<<resLits.size()<<" prem cnt: "<<premises->length());
  }
//  cout<<resLits.size()<<" ";
  if(_opt.satLearntSubsumptionResolution()) {
    doSubsumptionResolution(resLits, premises);
    LOG("sat_learnt_gen","post subs-res lit cnt: "<<resLits.size()<<" prem cnt: "<<premises->length());
  }
//  cout<<resLits.size()<<" ";

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
  LOG("sat_learnt","learnt clause: "<<(*res));
  return res;
}

TWLSolver::ClauseVisitResult TWLSolver::visitWatchedClause(Watch watch, unsigned var, unsigned& litIndex)
{
  CALL("TWLSolver::visitWatchedClause");

  if(isTrue(watch.blocker)) {
    return VR_NONE;
  }

  SATClause* cl = watch.cl;

  unsigned curWatchIndex=
      ((*cl)[0].var()==var) ? 0 : 1;
  ASS_EQ((*cl)[curWatchIndex].var(), var);
  ASS(isFalse((*cl)[curWatchIndex]));

  unsigned otherWatchIndex=1-curWatchIndex;

  SATLiteral otherWatched = (*cl)[otherWatchIndex];
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
    //The other wathed literal is undefined and there is also another undefined literal.
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
 * If conflict occurrs, return the clause that caused the conflict;
 * otherwise return 0.
 */
SATClause* TWLSolver::propagate(unsigned var)
{
  CALL("TWLSolver::propagate");

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

  LOG("sat_asmp","assumption point "<<lit);
}

void TWLSolver::makeChoiceAssignment(unsigned var, unsigned polarity)
{
  CALL("TWLSolver::makeChoiceAssignment");

  _level++;

  ASS(isUndefined(var));
  setAssignment(var, polarity);
  _assignmentLevels[var]=_level;
  _assignmentPremises[var]=0;
  _unitStack.push(USRec(var, true));
  schedulePropagation(var);

  LOG("sat_levels","choice point "<<var<<" to level "<<_level);
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

  _assignment[var] = AS_UNDEFINED;
  _assignmentPremises[var] = 0;

  _variableSelector->onVariableUnassigned(var);
}

void TWLSolver::addUnitClause(SATClause* cl)
{
  CALL("TWLSolver::addUnitClause");

  LOG("sat","adding unit "<<(*cl));

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

void TWLSolver::addClause(SATClause* cl)
{
  CALL("TWLSolver::addClause");

  LOG("sat","adding clause "<<(*cl));

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

  for(unsigned i=0;i<_varCnt;i++) {
    if(_assignment[i]!=AS_UNDEFINED) {
      ASS_LE(_assignmentLevels[i],_level);
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
  ASS_REP(polarity==0 || polarity==1, polarity);

  return _windex[2*var + polarity];
}

inline WatchStack& TWLSolver::getTriggeredWatchStack(unsigned var, PackedAsgnVal assignment)
{
  CALL("TWLSolver::getTriggeredWatchStack");
  ASS(assignment!=AS_UNDEFINED);

  return getWatchStack(var, 1-assignment);
}


/** Return true iff @c lit is true in the current assignment */
inline bool TWLSolver::isTrue(SATLiteral lit) const
{
  CALL("TWLSolver::isTrue");

  return _assignment[lit.var()] == static_cast<AsgnVal>(lit.polarity());
}

/** Return true iff @c lit is false in the current assignment */
inline bool TWLSolver::isFalse(SATLiteral lit) const
{
  CALL("TWLSolver::isFalse");

  return _assignment[lit.var()] == static_cast<AsgnVal>(lit.oppositePolarity());
}

/** Return true iff @c lit is undefined in the current assignment */
inline bool TWLSolver::isUndefined(SATLiteral lit) const
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

bool TWLSolver::getAssignment(unsigned var)
{
  CALL("TWLSolver::getAssignment");
  ASS_EQ(getStatus(), SATISFIABLE);
  ASS_L(var, _varCnt);
  ASS(!isUndefined(var));

  return isTrue(var);
}

void TWLSolver::printAssignment()
{
  CALL("TWLSolver::printAssignment");

  for(unsigned i=0;i<_varCnt;i++) {
    if(_assignment[i]==AS_UNDEFINED) {
      cout<<i<<"\t"<<static_cast<AsgnVal>(_assignment[i])<<endl;
    } else {
      cout<<i<<"\t"<<static_cast<AsgnVal>(_assignment[i])<<"\t"<<_assignmentLevels[i];
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

void TWLSolver::runSatLoop()
{
  CALL("TWLSolver::runSatLoop");

  _restartStrategy->reset();

  size_t conflictsBeforeRestart = _restartStrategy->getNextConflictCount();
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
      unsigned choiceVar;
      if(!_variableSelector->selectVariable(choiceVar)) {
        //We don't havething to propagate, nor any choice points. This means
        //we have fount an assignment.
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
      if(conflictsBeforeRestart==0) {
	restartASAP = true;
      }
      else {
	conflictsBeforeRestart--;
      }
      _variableSelector->onConflict();
      _clauseDisposer->onConflict();
      SATClause* learnt = getLearntClause(conflict);

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
	unsigned propBtLev = getBacktrackLevel(learnt);
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
}


}
