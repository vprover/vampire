/**
 * @file SAT/VariableSelector.cpp
 * Implements class VariableSelector.
 */

#include "SATClause.hpp"
#include "TWLSolver.hpp"

#include "VariableSelector.hpp"

using namespace SAT;

bool VariableSelector::isUndefined(unsigned var)
{
  CALL("VariableSelector::isUndefined");

  return _solver.isUndefined(var);
}

bool ActiveVariableSelector::selectVariable(unsigned& var)
{
  CALL("ActiveVariableSelector::selectVariable");

  do {
    if(_activityHeap.isEmpty()) {
      return false;
    }
    var = _activityHeap.popMostActive();
  } while(!isUndefined(var));
  return true;
}

void ActiveVariableSelector::ensureVarCnt(unsigned varCnt)
{
  CALL("ActiveVariableSelector::ensureVarCnt");

  VariableSelector::ensureVarCnt(varCnt);
  _activityHeap.ensureVarCnt(varCnt);
}

void ActiveVariableSelector::onInputClauseAdded(SATClause* cl)
{
  CALL("ActiveVariableSelector::onInputClauseAdded");

  unsigned clen = cl->length();
  for(unsigned i=0;i<clen;i++) {
    unsigned var = (*cl)[i].var();
    _activityHeap.markActivity(var);
  }
}



/////////////////////
// ArrayActiveVariableSelector

void ArrayActiveVariableSelector::onRestart()
{
  CALL("ArrayActiveVariableSelector::onRestart");

  for(unsigned i=0; i<_varCnt; i++) {
    _activities[i]/=2;
  }
}

bool ArrayActiveVariableSelector::selectVariable(unsigned& var)
{
  CALL("ArrayActiveVariableSelector::selectVariable");

  unsigned bestWCnt;
  int bestWCntI=-1;

  for(unsigned i=0;i<_varCnt;i++) {
    if(!isUndefined(i)) {
      continue;
    }
    unsigned wcnt=_activities[i];
    if(bestWCntI==-1 || wcnt>bestWCnt) {
      bestWCnt=wcnt;
      bestWCntI=i;
    }
  }
  if(bestWCntI!=-1) {
    var=bestWCntI;
    return true;
  }
  return false;
}

void ArrayActiveVariableSelector::onInputClauseAdded(SATClause* cl)
{
  CALL("ArrayActiveVariableSelector::onInputClauseAdded");

  unsigned clen = cl->length();
  for(unsigned i=0;i<clen;i++) {
    unsigned var = (*cl)[i].var();
    _activities[var]++;
  }
}

/////////////////////
// RLCVariableSelector

bool RLCVariableSelector::selectVariable(unsigned& var)
{
  CALL("RLCVariableSelector::selectVariable");

  SATClauseStack::TopFirstIterator lcit(_solver._learntClauses);
  while(lcit.hasNext()) {
    SATClause* cl = lcit.next();
    if(_solver.isTrue(cl)) {
      continue;
    }
    ASS(!_solver.isFalse(cl));

    unsigned bestVal;
    int bestVar = -1;
    unsigned clen = cl->length();
    for(unsigned i=0;i<clen;i++) {
      unsigned var = (*cl)[i].var();
      if(!isUndefined(var)) {
        continue;
      }
      unsigned curVal=_activities[var];
      if(bestVar==-1 || curVal>bestVal) {
	bestVal=curVal;
        bestVar=var;
      }
    }
    ASS_NEQ(bestVar,-1);
    var=bestVar;
    return true;
  }

  return ArrayActiveVariableSelector::selectVariable(var);
}

