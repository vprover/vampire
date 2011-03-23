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

TWLSolver::TWLSolver()
: _status(SATISFIABLE), _assignment(0), _assignmentLevels(0),
_windex(0), _unprocessed(0), _varCnt(0), _level(1)
{
  _variableSelector = new ActiveVariableSelector(*this);
//  _variableSelector = new ArrayActiveVariableSelector(*this);
//  _variableSelector = new RLCVariableSelector(*this);

//  _variableSelector = new AlternatingVariableSelector(*this, new ActiveVariableSelector(*this), new ArrayActiveVariableSelector(*this));

  _restartStrategy = new LubyRestartStrategy(100);
//  _restartStrategy = new MinisatRestartStrategy();

  _clauseDisposer = new MinisatClauseDisposer(*this);
//  _clauseDisposer = new GrowingClauseDisposer(*this);
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
  _unprocessed.expand(newVarCnt+1);

  _varCnt=newVarCnt;

  _variableSelector->ensureVarCnt(newVarCnt);
}


/**
 * Backtrack at least to level @c tgtLev
 */
void TWLSolver::backtrack(unsigned tgtLevel)
{
  CALL("TWLSolver::backtrack");
  ASSERT_VALID(*this);

  static Stack<USRec> marks;
  static ZIArray<unsigned> varMarkTgts;
  static ZIArray<AsgnVal> prevAssignments;
  static ZIArray<SATClause*> prevPremises;

  if(tgtLevel==_level) {
    return;
  }

  resetPropagation();

  if(tgtLevel==0) {
    throw UnsatException();
  }

  ASS(marks.isEmpty());

  USRec rec;
  for(;;) {
    rec=_unitStack.pop();
    if(rec.mark) {
      if(varMarkTgts[rec.var]==0 || varMarkTgts[rec.var]>rec.markTgtLevel) {
	marks.push(rec);
	varMarkTgts[rec.var]=rec.markTgtLevel;
      }
    }
    ASS(!rec.mark || rec.markTgtLevel>=_assignmentLevels[rec.var]);
    if(!isUndefined(rec.var) && (!rec.mark || rec.markedIsDefining)) {
      if(rec.mark) {
	prevAssignments[rec.var] = _assignment[rec.var];
	prevPremises[rec.var] = _assignmentPremises[rec.var];
      }
      undoAssignment(rec.var);
    }
    if(rec.choice) {
      _level--;
      incorporateUnprocessed();
      ASS_GE(_level, tgtLevel);
      if(_level==tgtLevel) {
	break;
      }
    }
  };

  while(marks.isNonEmpty()) {
    USRec rec=marks.pop();
    ASS_NEQ(varMarkTgts[rec.var], 0);
    ASS(rec.mark);
    if(varMarkTgts[rec.var]<rec.markTgtLevel) {
      continue;
    }
    varMarkTgts[rec.var]=0;

    if(rec.mark && rec.markTgtLevel>_level) {
      continue;
    }
    if(rec.mark && rec.markTgtLevel==_level) {
      rec.mark=false;
    }
    ASS_LE(_assignmentLevels[rec.var],_level);
    if(isUndefined(rec.var)) {
      setAssignment(rec.var, prevAssignments[rec.var]);
      _assignmentPremises[rec.var] = prevPremises[rec.var];
      //the _assignmentLevels[rec.var] value is properly assigned from
      //the previous time
      rec.markedIsDefining=true;

      schedulePropagation(rec.var);
    }

    _unitStack.push(rec);
  }

  ASS_EQ(_level, tgtLevel);

  LOG("backtracked to level "<<_level);
#if VDEBUG
  assertValid();
#endif
}

void TWLSolver::incorporateUnprocessed()
{
  CALL("TWLSolver::incorporateUnprocessed");

  Stack<SATClause*>& unp=_unprocessed[_level];
  while(unp.isNonEmpty()) {
    SATClause* cl=unp.pop();
    //unprocessed literals must already have literals
    //to be watched in the right place
    insertIntoWatchIndex(cl);
  }
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

void TWLSolver::doSubsumptionResolution(SATLiteralStack& lits)
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
	resolved = true;
	break;
      }
    }
    if(resolved) {
      litSet.remove(rLit.content());
      litIt.del();
    }
  }
}

void TWLSolver::doShallowMinimize(SATLiteralStack& lits, ArraySet& seenVars)
{
  CALL("TWLSolver::doShallowMinimize");

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
      if(!seenVars.find(premLit.var()) && getAssignmentLevel(premLit)>1) {
	redundant = false;
	break;
      }
    }
    if(redundant) {
      rit.del();
    }
  }
}

void TWLSolver::doDeepMinimize(SATLiteralStack& lits, ArraySet& seenVars)
{
  CALL("TWLSolver::doDeepMinimize");

  SATLiteralStack::Iterator rit(lits);
  while(rit.hasNext()) {
    SATLiteral resLit = rit.next();
    if(isRedundant(resLit, seenVars)) {
      rit.del();
    }
  }
}

bool TWLSolver::isRedundant(SATLiteral lit, ArraySet& seenVars)
{
  CALL("TWLSolver::isRedundant");

  static ArraySet varsSeenHere;
  varsSeenHere.ensure(_varCnt);
  varsSeenHere.reset();
  static Stack<unsigned> toDo;
  toDo.reset();

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
      return false;
    }
    SATClause::Iterator premLitIt(*cl);
    while(premLitIt.hasNext()) {
      SATLiteral premLit = premLitIt.next();
      unsigned premVar = premLit.var();
      if(seenVars.find(premVar) || getAssignmentLevel(premLit)==1) {
	continue;
      }
      toDo.push(premVar);
    }
  }
  return true;
}

SATClause* TWLSolver::getLearntClause(SATClause* conflictClause)
{
  CALL("TWLSolver::getLearntClause");
  ASS(isFalse(conflictClause));

  static ArraySet seenVars;
  seenVars.ensure(_varCnt);
  seenVars.reset();

  static SATLiteralStack resLits;
  static SATClauseStack toDo;
  resLits.reset();
  toDo.reset();

  toDo.push(conflictClause);
  while(toDo.isNonEmpty()) {
    SATClause* cl=toDo.pop();
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

//  cout<<resLits.size()<<" ";
//  doShallowMinimize(resLits, seenVars);
  doDeepMinimize(resLits, seenVars);
//  cout<<resLits.size()<<" ";
  doSubsumptionResolution(resLits);
//  cout<<resLits.size()<<" ";

  SATClause* res = SATClause:: fromStack(resLits);

#if VDEBUG
  {
    //we check that there is at most one literal on the current decision level
    bool curLevFound = false;
    SATLiteralStack::Iterator rlIt(resLits);
    while(rlIt.hasNext()) {
      SATLiteral lit = rlIt.next();
      if(getAssignmentLevel(lit)==_level) {
	ASS(!curLevFound);
	curLevFound = true;
      }
    }
  }
#endif

  ASS(isFalse(res));
  _learntClauses.push(res);
  env.statistics->learntSatClauses++;
//  cout<<res->toString()<<endl;
  recordClauseActivity(res);
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

  LOG("propagating "<<var<<" "<<_assignment[var]);
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
      unsigned uvar=undefLit.var();

      makeForcedAssignment(undefLit, cl);
      schedulePropagation(uvar);
      break;
    }
    case VR_NONE:
      break;
    }
  }
  return 0;
}

void TWLSolver::propagateAndBacktrackIfNeeded(unsigned var)
{
  CALL("TWLSolver::propagateAndBacktrackIfNeeded");

  SATClause* conflict = propagate(var);
  if(!conflict) {
    return;
  }
  unsigned btLevel = getBacktrackLevel(conflict);
  ASS_L(btLevel, _level);
  backtrack(btLevel);
}


void TWLSolver::addClauses(SATClauseIterator cit)
{
  CALL("TWLSolver::addClauses");

  LOG("");
  LOG("##############");

  if(_status==UNSATISFIABLE) {
    return;
  }

  try {
    while(cit.hasNext()) {
      SATClause* cl=cit.next();
      cl->setKept(true);
      if(cl->length()==1) {
	addUnitClause(cl);
      } else {
	addClause(cl);
      }
      _variableSelector->onInputClauseAdded(cl);
      _clauseDisposer->onNewInputClause(cl);
    }
    runSatLoop();

  } catch (UnsatException e)
  {
    _status=UNSATISFIABLE;
    return;
  }
}

void TWLSolver::setAssignment(unsigned var, unsigned polarity)
{
  CALL("TWLSolver::setAssignment");

  _assignment[var] = static_cast<AsgnVal>(polarity);
  _lastAssignments[var] = static_cast<AsgnVal>(polarity);
}

void TWLSolver::makeChoiceAssignment(unsigned var, unsigned polarity)
{
  CALL("TWLSolver::makeChoiceAssignment");

  _level++;
  _chosenVars[_level]=var;

  ASS(isUndefined(var));
  setAssignment(var, polarity);
  _assignmentLevels[var]=_level;
  _assignmentPremises[var]=0;
  _unitStack.push(USRec(var, true));

  LOG("choice point "<<var<<" to level "<<_level);
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

  LOG("adding unit "<<(*cl));

  SATLiteral lit=(*cl)[0];
  unsigned lvar=lit.var();

  if(isFalse(lit)) {
    do {
      unsigned btLevel=getBacktrackLevel(cl);
      ASS_NEQ(btLevel, _level);
      backtrack(btLevel);
    } while (isFalse(lit));
    ASS(isUndefined(lit))
  }
  ASS(!isFalse(lit));

  _assignmentLevels[lvar]=1;
  _assignmentPremises[lvar]=cl;
  if(isUndefined(lvar)) {
    setAssignment(lvar, lit.polarity());
    _unitStack.push( USRec(lvar, false, true, true, 1) );

    schedulePropagation(lvar);
  } else {
    ASS(isTrue(lit));
    _unitStack.push( USRec(lvar, false, true, false, 1) );
  }
}

/**
 * Handle clause which implies an assignment on earlier than the
 * current level.
 *
 * First literal of the clause must contain the variable whose
 * assignment is implied. Second is the literal with highest
 * assignment level in the rest of the clause (this level is the
 * level on which the assignment is implied by unit propagation).
 */
void TWLSolver::addMissingWatchLitClause(SATClause* cl)
{
  CALL("TWLSolver::addMissingWatchLitClause");

  LOG("mwl clause: "<<(*cl));
  LOG("--");

  SATLiteral wLit=(*cl)[0];
  SATLiteral swLit=(*cl)[1]; //second (pseudo-)watched literal

  unsigned wvar=wLit.var();

  ASS(isFalse(swLit));

  unsigned lowerWatchLevel=getAssignmentLevel(swLit);
  ASS_L(lowerWatchLevel, _level);

  ASS(isUndefined(wvar) || getAssignmentLevel(wLit)>lowerWatchLevel);

  _unprocessed[lowerWatchLevel].push(cl);

  _assignmentPremises[wvar]=cl;
  _assignmentLevels[wvar]=lowerWatchLevel;
  if( isUndefined(wLit) ) {
    setAssignment(wvar, wLit.polarity());
    _unitStack.push( USRec(wvar, false, true, true, lowerWatchLevel) );

    schedulePropagation(wvar);
  } else {
    ASS(isTrue(wLit));
    _unitStack.push( USRec(wvar, false, true, false, lowerWatchLevel) );
  }
  LOG("");
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

  LOG("adding clause "<<(*cl));

  unsigned clen=cl->length();
  ASS_G(clen,1);

  unsigned wCnt=selectTwoNonFalseLiterals(cl);

  if(wCnt==0) {
    //the added clause is false, so we need to backtrack to get some space
    //to fix the assignment

    //due to marked unit stack elements, one backtrack might not be enough
    for(;;) {
      unsigned btLev=getBacktrackLevel(cl);
      ASS_NEQ(btLev, _level);
      backtrack(btLev);

      if(!isUndefined((*cl)[0])) {
        //some other literal could have become undefined
        for(unsigned i=1;i<clen;i++) {
          if(isUndefined((*cl)[i])) {
            swap( (*cl)[0], (*cl)[i] );
            break;
          }
        }
      }

      if(isUndefined((*cl)[0])) {
        break;
      }
    }

    //we have changed assignments, so we need to bring the undefined and high assigned
    //literals to front
    wCnt = selectTwoNonFalseLiterals(cl);
    ASS_GE(wCnt,1); //now at least one literal should be undefined
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

  if(isTrue(wLit) && hLev>=getAssignmentLevel(wLit)) {
    insertIntoWatchIndex(cl);
  } else if(isUndefined(wLit) && hLev==_level) {
    makeForcedAssignment(wLit, cl);

    insertIntoWatchIndex(cl);
    schedulePropagation(wLit.var());
  } else {
    addMissingWatchLitClause(cl);
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

bool TWLSolver::pickForPropagation(unsigned& var)
{
  CALL("TWLSolver::pickForPropagation");

  if(_toPropagate.isEmpty()) {
    return false;
  }

  var = _toPropagate.pop_back();
  _propagationScheduled.remove(var);
  return true;
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
    if(rec.mark) {
      ASS_LE(_assignmentLevels[rec.var], rec.markTgtLevel);
    }
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

inline WatchStack& TWLSolver::getTriggeredWatchStack(unsigned var, AsgnVal assignment)
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

void TWLSolver::printAssignment()
{
  CALL("TWLSolver::printAssignment");

  for(unsigned i=0;i<_varCnt;i++) {
    if(_assignment[i]==AS_UNDEFINED) {
      cout<<i<<"\t"<<_assignment[i]<<endl;
    } else {
      cout<<i<<"\t"<<_assignment[i]<<"\t"<<_assignmentLevels[i];
      if(_assignmentPremises[i]) {
	cout<<"\t"<<(*_assignmentPremises[i])<<"\t"<<_assignmentPremises[i];
      }
      cout<<endl;
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

    unsigned propagatedVar;
    if(pickForPropagation(propagatedVar)) {
    }
    else if(_variableSelector->selectVariable(propagatedVar)) {
      AsgnVal asgn = _lastAssignments[propagatedVar];
      if(asgn==AS_UNDEFINED) {
	asgn = (getWatchStack(propagatedVar, 0).size()>getWatchStack(propagatedVar, 1).size()) ? AS_FALSE : AS_TRUE;
      }
      makeChoiceAssignment(propagatedVar, asgn);
    }
    else {
      //We don't havething to propagate, nor any choice points. This means
      //we have fount an assignment.
      break;
    }


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
	  throw UnsatException();
	}
	ASS(isUndefined(lit));
	makeForcedAssignment(lit, learnt);
	conflict = propagate(lvar);
	continue;
      }

      unsigned nonFalseLitCnt;
      do {
	unsigned propBtLev = getBacktrackLevel(learnt);
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
