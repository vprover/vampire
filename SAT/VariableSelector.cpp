
/*
 * File VariableSelector.cpp.
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
 * @file SAT/VariableSelector.cpp
 * Implements class VariableSelector.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "SATClause.hpp"
#include "TWLSolver.hpp"

#include "VariableSelector.hpp"

using namespace SAT;

bool VariableSelector::isUndefined(unsigned var)
{
  CALL("VariableSelector::isUndefined");

  ASS_G(var,0); ASS_LE(var,_varCnt);

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

void ActiveVariableSelector::ensureVarCount(unsigned varCnt)
{
  CALL("ActiveVariableSelector::ensureVarCount");

  VariableSelector::ensureVarCount(varCnt);
  _activityHeap.ensureVarCount(varCnt);
  // expand and initialise new entries with 0
  _niceness.expand(varCnt+1, 0);
}

void ActiveVariableSelector::onInputClauseAdded(SATClause* cl)
{
  CALL("ActiveVariableSelector::onInputClauseAdded");

  unsigned clen = cl->length();

  for(unsigned i=0;i<clen;i++) {
    SATLiteral lit = (*cl)[i];
    unsigned var = lit.var();
    // get niceness if not already got
    if(_niceness[var]==0){ 
      unsigned niceness = getNiceness(var);
      _niceness[var] = niceness;
    }
    _activityHeap.markActivity(var);
  }
}

/**
 * Uses source literal to compute the niceness for a SATLiteral
 * Note - higher is better i.e. a larger niceness value should indicate
 *        that we want to select this literal
 *
 * The general notion used here is that it is 'nicer' to have variables
 * and constants deeper in the literal. 
 *
 * Three separate ways of computing niceness have been implemented. These
 * should be compared and other options explored. 
 * 
 * @author Giles
 */
unsigned ActiveVariableSelector::getNiceness(unsigned var)
{
  CALL("ActiveVariableSelector::getNiceness");

  ASS_G(var,0); ASS_LE(var,_varCnt);

  // If niceness is switched off use 1
  if(_niceness_option == Options::Niceness::NONE){
    return 1;
  }

  // use source literal to compute niceness weight
  Literal* _source = _sourceMap.get(var); 

  // if it is null return 1 niceness
  // we assume that either all SATLiterals will have a niceness
  // score or none will
  if(!_source){
    return 1;
  }
  //We will do a Breadth-First search for variables or constants

  static Stack<const TermList*> _stack;
  _stack.reset();

  _stack.push(_source->args());

  unsigned level = 0;
  unsigned level_multiplier = 1;//change to make lower levels score more
  bool found = false;
  unsigned level_sum = 0;
  unsigned count = 0;
  bool divide = false;
  switch(_niceness_option){
    case Options::Niceness::NONE:
      return 1;
    case Options::Niceness::TOP:
      // Search for highest variable/constant
      while(!_stack.isEmpty() && !found){
        level++;
for(const TermList* t = _stack.pop(); !t->isEmpty(); t = t->next()){
          if(t->isVar()){
            found=true;
            break;
          }
          else{
            ASS(t->isTerm());
            const Term* trm = t->term();
            ASS(trm->shared());
            if(trm->ground()){
              found=true;
              break;
            }
            _stack.push(trm->args()); //breadth first, save args for later
          }
        }
      } 
      level = level*level_multiplier;
      RSTAT_MCTR_INC("nscore",level);
      return level;
    case Options::Niceness::AVERAGE:
      divide=true;
    case Options::Niceness::SUM:
      //sum the levels of all variables/constants
      while(!_stack.isEmpty()){
        level++;
        for(const TermList* t = _stack.pop(); !t->isEmpty(); t = t->next()){
          if(t->isVar()){
            level_sum += (level*level_multiplier);
          }
          else{
            ASS(t->isTerm());
            const Term* trm = t->term();
            ASS(trm->shared());
            if(trm->ground()){
              level_sum += (level*level_multiplier);
              count += 1;
            }
            _stack.push(trm->args()); //breadth first, save args for later
         }
        }
      }
      RSTAT_MCTR_INC("nscore",level_sum);
      // if we want average, we set divid=true earlier
      if(divide){ level_sum = (level_sum/count);}//This division will truncate
      return level_sum;
    default: ASSERTION_VIOLATION_REP2("Invalid niceness option: ",static_cast<int>(_niceness_option));
  }

  return 1;
}


/////////////////////
// ArrayActiveVariableSelector

void ArrayActiveVariableSelector::onRestart()
{
  CALL("ArrayActiveVariableSelector::onRestart");

  for(unsigned i=1; i<=_varCnt; i++) {
    _activities[i]/=2;
  }
}

bool ArrayActiveVariableSelector::selectVariable(unsigned& var)
{
  CALL("ArrayActiveVariableSelector::selectVariable");

  unsigned bestWCnt;
  int bestWCntI=-1;

  for(unsigned i=1;i<=_varCnt;i++) {
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

