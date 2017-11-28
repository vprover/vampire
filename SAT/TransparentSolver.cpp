
/*
 * File TransparentSolver.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file TransparentSolver.cpp
 * Implements class TransparentSolver.
 */

#include "SATClause.hpp"
#include "SATLiteral.hpp"

#include "TransparentSolver.hpp"

namespace SAT
{

TransparentSolver::TransparentSolver(SATSolver* inner)
  : _inner(inner)
{
}


void TransparentSolver::ensureVarCnt(unsigned newVarCnt)
{
  CALL("TransparentSolver::ensureVarCnt");

  _inner->ensureVarCnt(newVarCnt);
  _vars.expand(newVarCnt);
}

void TransparentSolver::addClauses(SATClauseIterator cit, bool onlyPropagate)
{
  CALL("TransparentSolver::addClauses");
  ASS(_assumptions.isEmpty());
  ASS(_unprocessed.isEmpty());
  ASS(_toBeAdded.isEmpty());

  _unprocessed.loadFromIterator(cit);
  
  processUnprocessed();

  flushClausesToInner(onlyPropagate);
}

void TransparentSolver::flushClausesToInner(bool onlyPropagate)
{
  CALL("TransparentSolver::flushClausesToInner");

  _inner->addClauses(pvi( SATClauseStack::Iterator(_toBeAdded) ), onlyPropagate);
  _toBeAdded.reset();
}

void TransparentSolver::processUnit(SATClause* cl)
{
  CALL("TransparentSolver::processUnit");

  SATLiteral lit = (*cl)[0];
  unsigned var = lit.var();
  VarInfo& vi = _vars[var];

  if(vi._unit) {
    if((*vi._unit)[0].polarity()==lit.polarity()) {
      //subsumed;
      return;
    }
    else {
      //we'll have a refutation
    }
  }
  else {
    vi._unit = cl;
    //this function cannot be called from the processUnprocessed function when we're handling
    //addAssumption, because units are never among watched clauses (and during addAssumption
    //we may handle only those)
    ASS(!vi._hasAssumption);
    if(!vi._unseen && vi._isPure) {
      if(vi._isPurePositive==lit.polarity()) {
	//watched clauses are subsumed
	vi._watched.reset();
      }
      else if(!tryToSweepPure(var, false)) {
	makeVarNonPure(var);
      }
    }
    if(vi._unseen) {
	vi._unseen = false;
	vi._isPure = true;
	vi._isPurePositive = lit.polarity();
    }
  }

  _toBeAdded.push(cl);
}

void TransparentSolver::makeVarNonPure(unsigned var)
{
  CALL("TransparentSolver::makeVarNonPure");
  ASS(!_vars[var]._unseen);
  ASS(_vars[var]._isPure);

  //move away as many watched clauses as possible
  NEVER(tryToSweepPure(var, true)); //we however can't remove all of them
  VarInfo& vi = _vars[var];
  _unprocessed.loadFromIterator( SATClauseStack::Iterator(vi._watched) );
  vi._watched.reset();
  vi._isPure = false;
}

void TransparentSolver::processUnprocessed()
{
  CALL("TransparentSolver::processUnprocessed");


  static Stack<unsigned> toUnpure;

  while(_unprocessed.isNonEmpty()) {
    SATClause* cl = _unprocessed.pop();

    if(cl->length()==1) {
      processUnit(cl);
      continue;
    }
    if(tryWatchOrSubsume(cl)) {
      continue;
    }

    //the clause is not pure, we try to swap polarity of some pure literals,
    //but if unsuccessful, we need to mark all literals occuring in clause
    //as non-pure (this may trigger further clause additions)

    toUnpure.reset();

    bool fixed = false;

    SATClause::Iterator it1(*cl);
    while(it1.hasNext()) {
      SATLiteral lit = it1.next();
      unsigned var = lit.var();
      ASS(!_vars[var]._unseen || _vars[var]._hasAssumption);
      ASS(!_vars[var]._hasAssumption || cl->length()>1);
      if(!_vars[var]._isPure) {
        continue;
      }
      if(tryToSweepPure(var, false)) {
        ALWAYS(tryWatchOrSubsume(cl));
        fixed = true;
        break;
      }
      toUnpure.push(var);
    }

    if(fixed) {
      continue;
    }
    _toBeAdded.push(cl);

    while(toUnpure.isNonEmpty()) {
      unsigned var = toUnpure.pop();
      makeVarNonPure(var);
    }

  }
}

/**
 * @param eager if false, we return false after the first failure
 *        to move a clause elsewhere
 * @param var ???
 */
bool TransparentSolver::tryToSweepPure(unsigned var, bool eager)
{
  CALL("TransparentSolver::trySweepPure");
  ASS(_vars[var]._isPure);

  VarInfo& vi = _vars[var];

  if(!eager && vi._unit) {
    return false;
  }

  SATClauseStack::Iterator wit(vi._watched);
  while(wit.hasNext()) {
    SATClause* cl = wit.next();
#if VDEBUG
    size_t wstackSize = vi._watched.size();
#endif
    bool wasMovedOut = tryWatchOrSubsume(cl, var);
    ASS_EQ(wstackSize, vi._watched.size()); //we assert we didn't put the watched clause here
    if(wasMovedOut) {
      wit.del();
    } else if(!eager) {
      return false;
    }
  }
  if(vi._watched.isEmpty() && !vi._unit) {
    vi._unseen = true;
    return true;
  }
  return false;
}

/**
 * Return true if clause was watched at some pure variable or subsumed.
 *
 * If forbiddenVar is non-zero,
 */
bool TransparentSolver::tryWatchOrSubsume(SATClause* cl, unsigned forbiddenVar)
{
  CALL("TransparentSolver::tryWatchOrSubsume");

  SATClause::Iterator it(*cl);
  while(it.hasNext()) {
    SATLiteral lit = it.next();
    unsigned var = lit.var();
    if(var==forbiddenVar) {
      continue;
    }
    VarInfo& vi = _vars[var];
    if(vi._unit) {
      if(lit.polarity()==(*vi._unit)[0].polarity()) {
	//clause is subsumed by unit
	return true;
      }
      else {
	continue;
      }
    }
    if(vi._hasAssumption && vi._assumedPolarity!=lit.polarity()) {
      continue;
    }
    if(vi._unseen) {
      vi._unseen = false;
      vi._isPure = true;
      vi._isPurePositive = lit.polarity();
    }
    if(vi._isPure && vi._isPurePositive==lit.polarity()) {
      ASS(!vi._isRewritten);
      ASS(!vi._unit);
      vi._watched.push(cl);
      return true;
    }
  }
  return false;
}

SATSolver::VarAssignment TransparentSolver::getAssignment(unsigned var)
{
  CALL("TransparentSolver::getAssignment");

  VarInfo& vi = _vars[var];

  if(vi._hasAssumption) {
    return  vi._assumedPolarity ? SATSolver::TRUE : SATSolver::FALSE;
  }
  VarAssignment res;
  if(!vi._unseen && vi._isPure) {
    res = vi._isPurePositive ? SATSolver::TRUE : SATSolver::FALSE;
  }
  else {
    res = _inner->getAssignment(var);
  }
  return res;
}

///////////////////////
// assumptions
//

void TransparentSolver::addInnerAssumption(SATLiteral lit, unsigned conflictCountLimit)
{
  CALL("TransparentSolver::addInnerAssumption");
  
  _inner->addAssumption(lit, conflictCountLimit);
}

void TransparentSolver::addAssumption(SATLiteral lit, unsigned conflictCountLimit)
{
  CALL("TransparentSolver::addAssumption");

  unsigned var = lit.var();
  VarInfo& vi = _vars[var];

  if(vi._hasAssumption) {
    if(vi._assumedPolarity==lit.polarity()) {
      //duplicate assumption, do nothing
    }
    else {
      //unsatisfiable assumptions
      addInnerAssumption(lit.opposite(), true);
      addInnerAssumption(lit, true);
      ASS_EQ(_inner->getStatus(), SATSolver::UNSATISFIABLE);
    }
    return;
  }

  _assumptions.push(lit);
  vi._hasAssumption = true;
  vi._assumedPolarity = lit.polarity();

  SATSolver::Status innerStatus = _inner->getStatus();
  if(innerStatus==SATSolver::UNSATISFIABLE) { return; }

  if(vi._unit || vi._unseen || !vi._isPure) {
    addInnerAssumption(lit, conflictCountLimit);
    return;
  }
  if(vi._isPurePositive==lit.polarity()) {
    return;
  }

  if(tryToSweepPure(var, false)) {
    addInnerAssumption(lit, conflictCountLimit);
    return;
  }

  //we assume the opposite of a pure variable, so the variable is no longer pure
  makeVarNonPure(var);
  processUnprocessed();
  //we have to retract assumptions in order to add clauses
  _inner->retractAllAssumptions();
  flushClausesToInner(true);

  SATLiteralStack::BottomFirstIterator ait(_assumptions);
  while(ait.hasNext()) {
    SATLiteral restoredLit = ait.next();
    bool last = !ait.hasNext();
    addInnerAssumption(restoredLit, last ? conflictCountLimit : 0);
  }
}

void TransparentSolver::retractAllAssumptions()
{
  CALL("TransparentSolver::retractAllAssumptions");

  _inner->retractAllAssumptions();
  while(_assumptions.isNonEmpty()) {
    SATLiteral lit = _assumptions.pop();
    unsigned var = lit.var();
    VarInfo& vi = _vars[var];
    ASS(vi._hasAssumption);
    ASS_EQ(vi._assumedPolarity,lit.polarity());
    vi._hasAssumption = false;
  }
}




}
