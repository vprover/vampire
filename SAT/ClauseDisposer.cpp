
/*
 * File ClauseDisposer.cpp.
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
 * @file ClauseDisposer.cpp
 * Implements class ClauseDisposer.
 */

#include <algorithm>

#include "Lib/BinaryHeap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Shell/Statistics.hpp"

#include "TWLSolver.hpp"

#include "ClauseDisposer.hpp"

namespace SAT
{

using namespace std;

unsigned ClauseDisposer::varCnt() const
{
  CALL("ClauseDisposer::varCnt");

  return _solver._varCnt;
}

unsigned ClauseDisposer::decisionLevel()
{
  CALL("ClauseDisposer::decisionLevel");

  return _solver._level;
}


SATClauseStack& ClauseDisposer::getLearntStack()
{
  CALL("ClauseDisposer::getLearntStack");

  return _solver._learntClauses;
}

DArray<WatchStack>& ClauseDisposer::getWatchedStackArray()
{
  CALL("ClauseDisposer::getWatchedStackArray");

  return _solver._windex;
}

SATClause* ClauseDisposer::getAssignmentPremise(unsigned var)
{
  CALL("ClauseDisposer::getAssignmentPremise");

  return _solver._assignmentPremises[var];
}

/**
 * Clean the 'kept' flag of all learnt clauses that are not used
 * as a justification for some assignment.
 */
void ClauseDisposer::markAllRemovableUnkept()
{
  CALL("ClauseDisposer::markAllRemovableUnkept");

  SATClauseStack::Iterator lrnIt(getLearntStack());
  while(lrnIt.hasNext()) {
    SATClause* cl = lrnIt.next();
    cl->setKept(false);
  }

  unsigned vc = varCnt();
  for(unsigned i=1; i<=vc; i++) {
    SATClause* cl = getAssignmentPremise(i);
    if(cl) {
      cl->setKept(true);
    }
  }
}

/**
 * We assume that all non-learnt clauses have their 'kept' flag
 * set to true.
 */
void ClauseDisposer::removeUnkept()
{
  CALL("ClauseDisposer::removeUnkept");

  unsigned watchCnt = (varCnt()+1)*2;
  DArray<WatchStack>& watches = getWatchedStackArray();

  for(unsigned i=2; i<watchCnt; i++) {
    WatchStack::Iterator wit(watches[i]);
    while(wit.hasNext()) {
      SATClause* cl = wit.next().cl;
      if(!cl->kept()) {
	wit.del();
      }
    }
  }

  SATClauseStack::StableDelIterator lrnIt(getLearntStack());
  while(lrnIt.hasNext()) {
    SATClause* cl = lrnIt.next();
    if(!cl->kept()) {
      lrnIt.del();
      cl->destroy();
    }
  }
}

struct ClauseActivityComparator
{
  static Comparison compare(SATClause* c1, SATClause* c2)
  {
//    return Int::compare(c1->activity()*c2->length(), c2->activity()*c1->length());
    return Int::compare(c1->activity(), c2->activity());
  }
};

void ClauseDisposer::keepMostActive(size_t numberOfKept, ActivityType minActivity)
{
  CALL("ClauseDisposer::keepMostActive");

  static BinaryHeap<SATClause*, ClauseActivityComparator> mah; //most active heap
  mah.reset();

  SATClauseStack::Iterator lrnIt(getLearntStack());
  while(lrnIt.hasNext()) {
    SATClause* cl = lrnIt.next();
    if(cl->activity()<minActivity) {
      continue;
    }
    mah.insert(cl);
    if(mah.size()>numberOfKept) {
	mah.pop();
    }
  }
  while(!mah.isEmpty()) {
    mah.pop()->setKept(true);
  }
}

void ClauseDisposer::keepBinary()
{
  CALL("ClauseDisposer::keepBinary");

  size_t idx = 0;
  SATClauseStack::Iterator lrnIt(getLearntStack());
  while(lrnIt.hasNext()) {
    SATClause* cl = lrnIt.next();
    if(cl->size()<=2) {
      cl->setKept(true);
    }
    idx++;
  }
}

///////////////////////////
// DecayingClauseDisposer

/**
 * Decay the importance of former conflicts
 */
void DecayingClauseDisposer::onConflict()
{
  CALL("DecayingClauseDisposer::onConflict");

  _inc *= _decayFactor;
  if(_inc<1e30f) {
    return;
  }

  _inc /= 1e30f;
  SATClauseStack::StableDelIterator lrnIt(getLearntStack());
  while(lrnIt.hasNext()) {
    SATClause* cl = lrnIt.next();
    cl->activity() /= 1e30f;
  }
}


///////////////////////////
// MinisatClauseDisposer

void MinisatClauseDisposer::onNewInputClause(SATClause* cl)
{
  CALL("MinisatClauseDisposer::onNewInputClause");

  DecayingClauseDisposer::onNewInputClause(cl);
//  if(cl->size()<3) {
//    return;
//  }
  _clauseCntAcc++;
  if(_clauseCntAcc>=4) {
    _survivorCnt += _clauseCntAcc/4;
    _clauseCntAcc = _clauseCntAcc%4;
  }
}

void MinisatClauseDisposer::onConflict()
{
  CALL("MinisatClauseDisposer::onConflict");

  DecayingClauseDisposer::onConflict();
//  cout<<"aa\n";
  _phaseIdx++;
  if(_phaseIdx>=_phaseLen) {
    _survivorCnt = _survivorCnt+max(_survivorCnt/10,static_cast<size_t>(1));
    _phaseIdx = 0;
    _phaseLen += _phaseLen/2;
//    cout<<getLearntStack().size()<<"  "<<_survivorCnt<<"  "
//	<<(env.statistics->learntSatLiterals/env.statistics->learntSatClauses)<<endl;
  }
}

void MinisatClauseDisposer::onSafeSpot()
{
  CALL("MinisatClauseDisposer::onSafeSpot");

  unsigned learntCnt = getLearntStack().size();

  if(static_cast<long>(learntCnt)-static_cast<long>(decisionLevel())>static_cast<long>(_survivorCnt)) {
    markAllRemovableUnkept();

    keepMostActive(learntCnt/2, _inc/learntCnt);
    keepBinary();

    removeUnkept();
//    cout<<"lco: "<<learntCnt<<" lcn: "<<getLearntStack().size()<<" sc: "<<_survivorCnt<<endl;
  }
}

///////////////////////////
// GrowingClauseDisposer

void GrowingClauseDisposer::onNewInputClause(SATClause* cl)
{
  CALL("GrowingClauseDisposer::onNewInputClause");

  DecayingClauseDisposer::onNewInputClause(cl);
  if(cl->size()<3) {
    return;
  }
  _clauseCntAcc++;
  if(_clauseCntAcc>=4) {
    _survivorCnt += _clauseCntAcc/4;
    _clauseCntAcc = _clauseCntAcc%4;
  }
}

void GrowingClauseDisposer::onConflict()
{
  CALL("GrowingClauseDisposer::onConflict");

  DecayingClauseDisposer::onConflict();

  _phaseIdx++;
  if(_phaseIdx>=_phaseLen) {
    _survivorCnt = _survivorCnt+max(_survivorCnt/10,static_cast<size_t>(1));
    _phaseIdx = 0;
    _phaseLen += _phaseLen/2;
//    cout<<getLearntStack().size()<<"  "<<_survivorCnt<<endl;
  }
}

void GrowingClauseDisposer::onRestart()
{
  CALL("GrowingClauseDisposer::onRestart");

  markAllRemovableUnkept();

  keepMostActive(_survivorCnt, 0);
  keepBinary();

  removeUnkept();

}


}
