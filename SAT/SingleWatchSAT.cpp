
/*
 * File SingleWatchSAT.cpp.
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
 * @file SingleWatchSAT.cpp
 * Implements class SingleWatchSAT.
 */

#include <algorithm>

#include "Lib/Allocator.hpp"
#include "Lib/Random.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Sort.hpp"
#include "Lib/Sort.hpp"

#include "SATClause.hpp"
#include "SATClauseSharing.hpp"
//#include "Inference.hpp"

#include "SingleWatchSAT.hpp"

namespace SAT {

using namespace Lib;

SingleWatchSAT::SingleWatchSAT(unsigned varCnt)
: refutation(0), _currTimeStamp(1), _varCnt(varCnt),
_asgnVals(varCnt), _levelInfos(varCnt), _conflicts(varCnt), _unitClauses(32)
{
  CALL("SingleWatchSAT::SingleWatchSAT");

  _asgnVals.init(_varCnt, false);

  _watched=static_cast<ClauseStack*>(ALLOC_KNOWN(_varCnt*sizeof(ClauseStack), "ClauseStack"));
  _reeval=static_cast<ClauseStack*>(ALLOC_KNOWN(_varCnt*sizeof(ClauseStack), "ClauseStack"));
  for(unsigned i=0;i<_varCnt;i++) {
    new (&_watched[i]) ClauseStack(8);
    new (&_reeval[i]) ClauseStack(8);
  }
}

SingleWatchSAT::~SingleWatchSAT()
{
  CALL("SingleWatchSAT::~SingleWatchSAT");

  for(unsigned i=0;i<_varCnt;i++) {
//    cout<<i<<"\t"<<_posClauses[i].size()<<"\t"<<_negClauses[i].size()<<"\t"<<_asgnInfos[i].minVar<<"\t"<<_asgnInfos[i].maxVar<<"\n";
    _watched[i].~ClauseStack();
    _reeval[i].~ClauseStack();
  }
  DEALLOC_KNOWN(_watched, _varCnt*sizeof(ClauseStack), "ClauseStack");
  DEALLOC_KNOWN(_reeval, _varCnt*sizeof(ClauseStack), "ClauseStack");
}


bool SingleWatchSAT::loadClauses(SATClauseIterator clauses)
{
  CALL("SingleWatchSAT::loadClauses");

  while(clauses.hasNext()) {
    SATClause* cl=clauses.next();
//    cout<<(*cl)<<endl;
    if(cl->isEmpty()) {
      refutation=cl;
      termination=REFUTATION;
      return false;
    }
    incorporate(cl);
  }
  return true;
}

void SingleWatchSAT::reset()
{
  CALL("SingleWatchSAT::reset");

  SATClauseSharing::getInstance()->wipe();

  _currTimeStamp=1;
}

bool isLearnt(SATClause* cl)
{
  return !cl->kept();
}

SATClauseIterator SingleWatchSAT::learntClauses()
{
  CALL("SingleWatchSAT::learntClauses");

  return pvi( getFilteredIterator(SATClauseSharing::getInstance()->content(), isLearnt) );
}

//struct ClauseConflictnessComparator {
//  static Comparison compare(SATClause* cl1, SATClause* cl2) {
//    return Int::compare(cl2->conflicts(), cl1->conflicts());
//  }
//};

bool SingleWatchSAT::earlyTermination()
{
  CALL("SingleWatchSAT::earlyTermination");

  static int counter=0;


  if(_timeLimit && counter++ == 1000) {
    int elapsed=env.timer->elapsedMilliseconds()-_startTime;
    int remaining=_timeLimit-elapsed;
    counter=0;
    if(remaining<=0) {
      termination=TIME_LIMIT;
      return true;
    }
  }

  return false;
}


/**
 * In case time stamp is going to overflow, modify all
 * structures, so we can again start timestamping from 1.
 */
void SingleWatchSAT::resetTimeStamp()
{
  CALL("SingleWatchSAT::resetTimeStamp");

  INVALID_OPERATION("Resetting timestamp not supported.");
}

/**
 * Create a resolved clause.
 */
SATClause* SingleWatchSAT::resolveClauses(SATClause* c1, SATClause* c2)
{
  CALL("SingleWatchSAT::resolveClauses");

  unsigned newLen=c1->length()+c2->length()-2;
  static DArray<SATLiteral> nLits(32);
  nLits.ensure(newLen);

  SATLiteral* l1=&(*c1)[1];
  SATLiteral* l1Stop=&(*c1)[c1->length()];
  SATLiteral* l2=&(*c2)[1];
  SATLiteral* l2Stop=&(*c2)[c2->length()];

  //Here we merge literals of premise clauses so that we get
  //sorted result in linear time.
  unsigned next=0;
  while(l1!=l1Stop || l2!=l2Stop) {
    while( l1!=l1Stop && (l2==l2Stop || l1->var() > l2->var()) ) {
      nLits[next++]=*(l1++);
    }
    while( l2!=l2Stop && (l1==l1Stop || l1->var() < l2->var()) ) {
      nLits[next++]=*(l2++);
    }
    while( l1!=l1Stop && l2!=l2Stop && l1->var()==l2->var()) {
      ASS_EQ(l1->polarity(), l2->polarity());
      nLits[next++]=*(l1++);
      l2++;
      newLen--;
    }
  }

  SATClause* res=new(newLen) SATClause(newLen, false);

  for(unsigned i=0;i<newLen;i++) {
    (*res)[i]=nLits[i];
  }

  res->resetSATAlgorithmData();

  res=SATClauseSharing::getInstance()->insert(res);
  res->incGenCounter();


//  if(newLen<3) {
//    cout<<(*res)<<endl;
//  }
  return res;
}

inline
int SingleWatchSAT::evalTail(SATClause* cl)
{
  CALL("SingleWatchSAT::reevalTail");
  ASS_G(cl->length(),1);

  SATLiteral* l0=&(*cl)[0];
  SATLiteral* lit=&(*cl)[cl->length()-1];
  while(lit!=l0) {
    if(_asgnVals[lit->var()]==lit->isPositive()) {
      return (int)lit->var();
    }
    lit--;
  }
  return -1;
}

/**
 * Incorporate a clause into the right _reeval[i] stack.
 */
void SingleWatchSAT::incorporate(SATClause* cl)
{
  CALL("SingleWatchSAT::incorporate");
  ASS_G(cl->length(),1);
  ASS(cl->kept());

  cl->resetSATAlgorithmData();

  unsigned i=(*cl)[1].var();
  ASS_L(i, _varCnt);
  _reeval[i].push(cl);
}

void SingleWatchSAT::performDetermination(SATClause* cl)
{
  SATLiteral maxLit=(*cl)[0];
  unsigned tgtLev=maxLit.var();
  bool tgtPos=maxLit.isPositive();
  LevelInfo& tgtLvlInfo=_levelInfos[tgtLev];

  if(_asgnVals[tgtLev]!=tgtPos) {
    while(_watched[tgtLev].isNonEmpty()) {
      SATClause* wcl=_watched[tgtLev].pop();
      ASS(wcl->kept() || wcl->getGenCounter()>0);
      if(wcl->kept() || wcl->length()<3 || wcl->getGenCounter()>14) {
	putForReevaluation(wcl);
      }
    }

    _asgnVals[tgtLev]=tgtPos;
    nextTimeStamp();
    tgtLvlInfo.changeTime=_currTimeStamp;
    tgtLvlInfo.visitTime=_currTimeStamp;
  }
  tgtLvlInfo.determinant=cl;
  tgtLvlInfo.determiningTime=_currTimeStamp;
}

SATClause* SingleWatchSAT::handleUnitConflict(SATClause* cl)
{
  CALL("SingleWatchSAT::handleUnitConflict");
  ASS_EQ(cl->length(),1);

  _unitClauses.push(cl);

  SATLiteral lit=(*cl)[0];
  unsigned i=lit.var();
  ASS_NEQ(lit.isPositive(), _asgnVals[i]);
  SATClause* res;
  if(isDetermined(i)) {
    SATClause* det=_levelInfos[i].determinant;

    if(det->length()==1) {
      return new(0) SATClause(0, false);
    }

    res=_levelInfos[i].determinant;
  } else {
    res=0;
  }
  performDetermination(cl);

  return res;
}

void SingleWatchSAT::putForReevaluation(SATClause* cl)
{
  ASS_G(cl->length(),1);
  unsigned lvl=(*cl)[1].var();
  _reeval[lvl].push(cl);

  if(lvl<_lowestUnevaluated) {
    _lowestUnevaluated=lvl;
  }
}


void SingleWatchSAT::satisfy(int timeLimit)
{
  CALL("SingleWatchSAT::satisfy");

  _timeLimit=timeLimit;
  if(timeLimit) {
    _startTime=env.timer->elapsedMilliseconds();
    _unusedRemovalCnt=0;
  }
  _conflicts.init(_varCnt, 0);

  _level=0;

  while(_level!=_varCnt) {
    LevelInfo& lvlInfo=_levelInfos[_level];
    nextTimeStamp();
    lvlInfo.visitTime=_currTimeStamp;

    _lowestUnevaluated=_level;

    while(_reeval[_level].isNonEmpty()) {
      SATClause* cl=_reeval[_level].pop();
      ASS_EQ((*cl)[1].var(), _level);
      int trueVal=evalTail(cl);
      if(trueVal>=0) {
	_watched[trueVal].push(cl);
      } else {
	SATLiteral maxLit=(*cl)[0];
	unsigned tgtLev=maxLit.var();
	unsigned tgtPos=maxLit.isPositive();
	LevelInfo& tgtLvlInfo=_levelInfos[tgtLev];

	if(_asgnVals[tgtLev]!=tgtPos && isDetermined(tgtLev)) {
	  _reeval[_level].push(cl);
	  //we have a conflict at level tgtLev

	  _conflicts[tgtLev]++;

	  SATClause* resCl=resolveClauses(cl, tgtLvlInfo.determinant);
	  if(resCl->length()==1) {
	    resCl=handleUnitConflict(resCl); //can change _lowestUnevaluated
	    if(resCl && resCl->isEmpty()) {
	      refutation=resCl;
	      termination=REFUTATION;
	      return;
	    }
	  }
	  if(resCl) {
	    ASS_EQ((*resCl)[0].var(), _level);
	    ASS_NEQ((*resCl)[0].isPositive(),_asgnVals[_level]);
	    putForReevaluation(resCl); //can change _lowestUnevaluated
	    ASS_L(_lowestUnevaluated, _level);
	  }
	} else {
	  if(!isDetermined(tgtLev)) {
	    performDetermination(cl); //can change _lowestUnevaluated
	  }
	  _watched[tgtLev].push(cl);
	}
	if(_lowestUnevaluated<_level) {
	  break;
	}
      }
    }
    lvlInfo.visitTime=_currTimeStamp;
    if(_lowestUnevaluated<_level) {
      _level=_lowestUnevaluated;
    } else {
      ASS(_reeval[_level].isEmpty());
      _level++;
    }

    if(earlyTermination()) {
      return;
    }
  }

  termination=SATISFIABLE;
}

};
