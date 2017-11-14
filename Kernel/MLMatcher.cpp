
/*
 * File MLMatcher.cpp.
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
 * @file MLMatcher.cpp
 * Implements class MLMatcher.
 */

#include <algorithm>
#include <utility>

#include "Lib/Backtrackable.hpp"
#include "Lib/BacktrackIterators.hpp"
#include "Lib/BinaryHeap.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Hash.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaarrays.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/Stack.hpp"
#include "Lib/TriangularArray.hpp"

#include "Clause.hpp"
#include "Matcher.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "MLMatcher.hpp"

#if VDEBUG
#include <iostream>
#include "Test/Output.hpp"
using namespace std;
#endif

#define TRACE_LONG_MATCHING 0
#if TRACE_LONG_MATCHING
#include "Lib/Timer.hpp"
#endif

namespace Kernel
{

using namespace Lib;

typedef DHMap<unsigned,unsigned, IdentityHash> UUMap;


namespace MLMatcher_AUX
{

/**
 * Binder that stores bindings into a specified array. To be used
 * with MatchingUtils template methods.
 */
struct ArrayStoringBinder
{
  ArrayStoringBinder(TermList* arr, UUMap& v2pos)
  : _arr(arr), _v2pos(v2pos) {}

  bool bind(unsigned var, TermList term)
  {
    _arr[_v2pos.get(var)]=term;
    return true;
  }

  void specVar(unsigned var, TermList term)
  { ASSERTION_VIOLATION; }
private:
  TermList* _arr;
  UUMap& _v2pos;
};

bool createLiteralBindings(Literal* baseLit, LiteralList* alts, Clause* instCl, Literal* resolvedLit,
    unsigned*& boundVarData, TermList**& altBindingPtrs, TermList*& altBindingData)
{
  CALL("createLiteralBindings");

  static UUMap variablePositions;
  static BinaryHeap<unsigned,Int> varNums;
  variablePositions.reset();
  varNums.reset();

  VariableIterator bvit(baseLit);
  while(bvit.hasNext()) {
    unsigned var=bvit.next().var();
    varNums.insert(var);
  }

  unsigned nextPos=0;
  while(!varNums.isEmpty()) {
    unsigned var=varNums.pop();
    while(!varNums.isEmpty() && varNums.top()==var) {
      varNums.pop();
    }
    if(variablePositions.insert(var,nextPos)) {
      *(boundVarData++)=var;
      nextPos++;
    }
  }
  unsigned numVars=nextPos;

  LiteralList::Iterator ait(alts);
  while(ait.hasNext()) {
    //handle multiple matches in equality!
    Literal* alit=ait.next();
    if(alit==resolvedLit) {
      continue;
    }
    if(alit->isEquality()) {
      //we must try both possibilities
      if(MatchingUtils::matchArgs(baseLit,alit)) {
	ArrayStoringBinder binder(altBindingData, variablePositions);
	MatchingUtils::matchArgs(baseLit,alit,binder);
	*altBindingPtrs=altBindingData;
	altBindingPtrs++;
	altBindingData+=numVars;
	if(resolvedLit) {
	  new(altBindingData++) TermList((size_t)0);
	} else {
	  //add pointer to the literal at
	  //the end of the binding sequance
	  new(altBindingData++) TermList((size_t)instCl->getLiteralPosition(alit));
	}
      }
      if(MatchingUtils::matchReversedArgs(baseLit, alit)) {
	ArrayStoringBinder binder(altBindingData, variablePositions);
	MatchingUtils::matchTerms(*baseLit->nthArgument(0),*alit->nthArgument(1),binder);
	MatchingUtils::matchTerms(*baseLit->nthArgument(1),*alit->nthArgument(0),binder);

	*altBindingPtrs=altBindingData;
	altBindingPtrs++;
	altBindingData+=numVars;
	if(resolvedLit) {
	  new(altBindingData++) TermList((size_t)0);
	} else {
	  //add pointer to the literal at
	  //the end of the binding sequance
	  new(altBindingData++) TermList((size_t)instCl->getLiteralPosition(alit));
	}
      }

    } else {
      if(numVars) {
	ArrayStoringBinder binder(altBindingData, variablePositions);
	ALWAYS(MatchingUtils::matchArgs(baseLit,alit,binder));
      }

      *altBindingPtrs=altBindingData;
      altBindingPtrs++;
      altBindingData+=numVars;
      if(resolvedLit) {
        new(altBindingData++) TermList((size_t)0);
      } else {
        //add index of the literal in instance clause at
        //the end of the binding sequence
        new(altBindingData++) TermList((size_t)instCl->getLiteralPosition(alit));
      }
    }
  }
  if(resolvedLit && resolvedLit->complementaryHeader()==baseLit->header()) {
    if(!baseLit->arity() || MatchingUtils::matchArgs(baseLit,resolvedLit)) {
      if(numVars) {
	ArrayStoringBinder binder(altBindingData, variablePositions);
	MatchingUtils::matchArgs(baseLit,resolvedLit,binder);
      }
      *altBindingPtrs=altBindingData;
      altBindingPtrs++;
      altBindingData+=numVars;
      new(altBindingData++) TermList((size_t)1);
    }
    if(baseLit->isEquality() && MatchingUtils::matchReversedArgs(baseLit, resolvedLit)) {
      ArrayStoringBinder binder(altBindingData, variablePositions);
      MatchingUtils::matchTerms(*baseLit->nthArgument(0),*resolvedLit->nthArgument(1),binder);
      MatchingUtils::matchTerms(*baseLit->nthArgument(1),*resolvedLit->nthArgument(0),binder);

      *altBindingPtrs=altBindingData;
      altBindingPtrs++;
      altBindingData+=numVars;
      new(altBindingData++) TermList((size_t)1);
    }

  }
  return true;
}

struct MatchingData {
  unsigned len;
  unsigned* varCnts;
  unsigned** boundVarNums;
  /**
   * TermList[] corresponding to an alternative contains binding
   * for each variable of the base literal, and then one element
   * identifying the alternative literal itself.
   */
  TermList*** altBindings;
  TriangularArray<unsigned>* remaining;
  unsigned* nextAlts;

  TriangularArray<pair<int,int>* >* intersections;

  Literal** bases;
  LiteralList** alts;
  Clause* instance;
  Literal* resolvedLit;

  unsigned* boundVarNumStorage;
  TermList** altBindingPtrStorage;
  TermList* altBindingStorage;
  pair<int,int>* intersectionStorage;

  enum InitResult {
    OK,
    MUST_BACKTRACK,
    NO_ALTERNATIVE
  };

  unsigned getRemainingInCurrent(unsigned bi)
  {
    return remaining->get(bi,bi);
  }
  unsigned getAltRecordIndex(unsigned bi, unsigned alti)
  {
    return static_cast<unsigned>(altBindings[bi][alti][varCnts[bi]].content());
  }

  /**
   * Return true if binding @b b1Index -th base literal that binds variables
   * to terms stored in @b i1Bindings is compatible to binding @b b2Index -th
   * base literal that binds variables to terms stored in
   * @b altBindings[b2Index][i2AltIndex] .
   */
  bool compatible(unsigned b1Index, TermList* i1Bindings,
	unsigned b2Index, unsigned i2AltIndex, pair<int,int>* iinfo)
  {
    CALL("MatchingData::compatible");

    TermList* i2Bindings=altBindings[b2Index][i2AltIndex];

    while(iinfo->first!=-1) {
      if(i1Bindings[iinfo->first]!=i2Bindings[iinfo->second]) {
	return false;
      }
      iinfo++;
    }
    return true;
  }

  bool bindAlt(unsigned bIndex, unsigned altIndex)
  {
    TermList* curBindings=altBindings[bIndex][altIndex];
    for(unsigned i=bIndex+1; i<len; i++) {
      if(!isInitialized(i)) {
	break;
      }
      pair<int,int>* iinfo=getIntersectInfo(bIndex, i);
      unsigned remAlts=remaining->get(i,bIndex);

      if(iinfo->first!=-1) {
	for(unsigned ai=0;ai<remAlts;ai++) {
	  if(!compatible(bIndex,curBindings,i,ai,iinfo)) {
	    remAlts--;
	    std::swap(altBindings[i][ai], altBindings[i][remAlts]);
	    ai--;
	  }
	}
      }
      if(remAlts==0) {
	return false;
      }
      remaining->set(i,bIndex+1,remAlts);
    }
    return true;
  }

  pair<int,int>* getIntersectInfo(unsigned b1, unsigned b2)
  {
    ASS_L(b1, b2);
    pair<int,int>* res=intersections->get(b2,b1);
    if( res ) {
      return res;
    }
    intersections->set(b2,b1, intersectionStorage);
    res=intersectionStorage;

    unsigned b1vcnt=varCnts[b1];
    unsigned b2vcnt=varCnts[b2];
    unsigned* b1vn=boundVarNums[b1];
    unsigned* b1vnStop=boundVarNums[b1]+b1vcnt;
    unsigned* b2vn=boundVarNums[b2];
    unsigned* b2vnStop=boundVarNums[b2]+b2vcnt;

    int b1VarIndex=0;
    int b2VarIndex=0;
    while(true) {
      while(b1vn!=b1vnStop && *b1vn<*b2vn) { b1vn++; b1VarIndex++; }
      if(b1vn==b1vnStop) { break; }
      while(b2vn!=b2vnStop && *b1vn>*b2vn) { b2vn++; b2VarIndex++; }
      if(b2vn==b2vnStop) { break; }
      if(*b1vn==*b2vn) {
	intersectionStorage->first=b1VarIndex;
	intersectionStorage->second=b2VarIndex;
	intersectionStorage++;

        b1vn++; b1VarIndex++;
        b2vn++; b2VarIndex++;
        if(b1vn==b1vnStop || b2vn==b2vnStop) { break; }
      }
    }

    intersectionStorage->first=-1;
    intersectionStorage++;

    return res;
  }

  bool isInitialized(unsigned bIndex) {
    return boundVarNums[bIndex];
  }

  InitResult ensureInit(unsigned bIndex)
  {
    CALL("MatchingData::ensureInit");

    if(!isInitialized(bIndex)) {
      boundVarNums[bIndex]=boundVarNumStorage;
      altBindings[bIndex]=altBindingPtrStorage;
      ALWAYS(createLiteralBindings(bases[bIndex], alts[bIndex], instance, resolvedLit,
	  boundVarNumStorage, altBindingPtrStorage, altBindingStorage));
      varCnts[bIndex]=boundVarNumStorage-boundVarNums[bIndex];

      unsigned altCnt=altBindingPtrStorage-altBindings[bIndex];
      if(altCnt==0) {
	return NO_ALTERNATIVE;
      }
      remaining->set(bIndex, 0, altCnt);

      unsigned remAlts=0;
      for(unsigned pbi=0;pbi<bIndex;pbi++) { //pbi ~ previous base index
	pair<int,int>* iinfo=getIntersectInfo(pbi, bIndex);
        remAlts=remaining->get(bIndex, pbi);

        if(iinfo->first!=-1) {
          TermList* pbBindings=altBindings[pbi][nextAlts[pbi]-1];
          for(unsigned ai=0;ai<remAlts;ai++) {
            if(!compatible(pbi, pbBindings, bIndex, ai, iinfo)) {
              remAlts--;
              std::swap(altBindings[bIndex][ai], altBindings[bIndex][remAlts]);
              ai--;
            }
          }
        }
        remaining->set(bIndex,pbi+1,remAlts);
      }
      if(bIndex>0 && remAlts==0) {
        return MUST_BACKTRACK;
      }
    }
    return OK;
  }

};


static DArray<Literal*> s_baseLits(32);
static DArray<LiteralList*> s_altsArr(32);

static DArray<unsigned> s_varCnts(32);
static DArray<unsigned*> s_boundVarNums(32);
static DArray<TermList**> s_altPtrs(32);
static TriangularArray<unsigned> s_remaining(32);
static TriangularArray<pair<int,int>* > s_intersections(32);
static DArray<unsigned> s_nextAlts(32);


static DArray<unsigned> s_boundVarNumData(64);
static DArray<TermList*> s_altBindingPtrs(128);
static DArray<TermList> s_altBindingsData(256);
static DArray<pair<int,int> > s_intersectionData(128);

static MatchingData s_matchingData;

MatchingData* getMatchingData(Literal** baseLits0, unsigned baseLen, Clause* instance, LiteralList** alts,
	Literal* resolvedLit)
{
  CALL("getMatchingData");

  s_baseLits.initFromArray(baseLen,baseLits0);
  s_altsArr.initFromArray(baseLen,alts);

  s_varCnts.ensure(baseLen);
  s_boundVarNums.init(baseLen,0);
  s_altPtrs.ensure(baseLen);
  s_remaining.setSide(baseLen);
  s_nextAlts.ensure(baseLen);

  s_intersections.setSide(baseLen);
  s_intersections.zeroAll();

  //number of base literals that have zero alternatives
  //(not counting the resolved literal)
  unsigned zeroAlts=0;
  //number of base literals that have at most one alternative
  //(not counting the resolved literal)
  unsigned singleAlts=0;
  size_t baseLitVars=0;
  size_t altCnt=0;
  size_t altBindingsCnt=0;

  unsigned mostDistVarsLit=0;
  unsigned mostDistVarsCnt=s_baseLits[0]->getDistinctVars();

  for(unsigned i=0;i<baseLen;i++) {
    unsigned distVars=s_baseLits[i]->getDistinctVars();
//    unsigned distVars=s_baseLits[i]->vars(); //an upper estimate is enough

    baseLitVars+=distVars;
    unsigned currAltCnt=0;
    LiteralList::Iterator ait(s_altsArr[i]);
    while(ait.hasNext()) {
      currAltCnt++;
      if(ait.next()->commutative()) {
	currAltCnt++;
      }
    }
    altCnt+=currAltCnt+2; //the +2 is for the resolved literal (it can be commutative)
    altBindingsCnt+=(distVars+1)*(currAltCnt+2);

    if(currAltCnt==0) {
      if(zeroAlts!=i) {
	if(singleAlts!=zeroAlts) {
	  std::swap(s_baseLits[singleAlts],s_baseLits[zeroAlts]);
	  std::swap(s_altsArr[singleAlts],s_altsArr[zeroAlts]);
	}
	std::swap(s_baseLits[i],s_baseLits[zeroAlts]);
	std::swap(s_altsArr[i],s_altsArr[zeroAlts]);
	if(mostDistVarsLit==singleAlts) {
	  mostDistVarsLit=i;
	}
      }
      zeroAlts++;
      singleAlts++;
    } else if(currAltCnt==1 && !(resolvedLit && resolvedLit->couldBeInstanceOf(s_baseLits[i], true)) ) {
      if(singleAlts!=i) {
	std::swap(s_baseLits[i],s_baseLits[singleAlts]);
	std::swap(s_altsArr[i],s_altsArr[singleAlts]);
	if(mostDistVarsLit==singleAlts) {
	  mostDistVarsLit=i;
	}
      }
      singleAlts++;
    } else if(i>0 && mostDistVarsCnt<distVars) {
      mostDistVarsLit=i;
      mostDistVarsCnt=distVars;
    }
  }
  if(mostDistVarsLit>singleAlts) {
    std::swap(s_baseLits[mostDistVarsLit],s_baseLits[singleAlts]);
    std::swap(s_altsArr[mostDistVarsLit],s_altsArr[singleAlts]);
  }

  s_boundVarNumData.ensure(baseLitVars);
  s_altBindingPtrs.ensure(altCnt);
  s_altBindingsData.ensure(altBindingsCnt);
  s_intersectionData.ensure((baseLitVars+baseLen)*baseLen);

  s_matchingData.len=baseLen;
  s_matchingData.varCnts=s_varCnts.array();
  s_matchingData.boundVarNums=s_boundVarNums.array();
  s_matchingData.altBindings=s_altPtrs.array();
  s_matchingData.remaining=&s_remaining;
  s_matchingData.nextAlts=s_nextAlts.array();
  s_matchingData.intersections=&s_intersections;


  s_matchingData.bases=s_baseLits.array();
  s_matchingData.alts=s_altsArr.array();
  s_matchingData.instance=instance;
  s_matchingData.resolvedLit=resolvedLit;

  s_matchingData.boundVarNumStorage=s_boundVarNumData.array();
  s_matchingData.altBindingPtrStorage=s_altBindingPtrs.array();
  s_matchingData.altBindingStorage=s_altBindingsData.array();
  s_matchingData.intersectionStorage=s_intersectionData.array();

  return &s_matchingData;
}

}

using namespace MLMatcher_AUX;

/**
 *
 */
bool MLMatcher::canBeMatched(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts,
	Literal* resolvedLit, bool multiset)
{
  CALL("MLMatcher::canBeMatched");

  MatchingData* md=getMatchingData(baseLits, baseLen, instance, alts, resolvedLit);
  if(!md) {
    return false;
  }
  unsigned instLen = instance->length();

  static DArray<unsigned> matchRecord(32);
  unsigned matchRecordLen=resolvedLit?2:instLen;
  matchRecord.init(matchRecordLen,0xFFFFFFFF);


  unsigned matchedLen=md->len;

  md->nextAlts[0]=0;
  unsigned currBLit=0;

  int counter=0;

binding_start:
  while(true) {
    MatchingData::InitResult ires=md->ensureInit(currBLit);
    if(ires!=MatchingData::OK) {
      if(ires==MatchingData::MUST_BACKTRACK) {
	currBLit--;
	continue;
      } else {
	ASS_EQ(ires,MatchingData::NO_ALTERNATIVE);
	return false;
      }
    }

    unsigned maxAlt=md->getRemainingInCurrent(currBLit);
    while(md->nextAlts[currBLit]<maxAlt &&
	    ( (multiset &&
		    matchRecord[md->getAltRecordIndex(currBLit, md->nextAlts[currBLit])]<currBLit) ||
	    !md->bindAlt(currBLit,md->nextAlts[currBLit]) ) ) {
      md->nextAlts[currBLit]++;
    }
    if(md->nextAlts[currBLit] < maxAlt) {
      unsigned matchRecordIndex=md->getAltRecordIndex(currBLit, md->nextAlts[currBLit]);
      for(unsigned i=0;i<matchRecordLen;i++) {
	if(matchRecord[i]==currBLit) {
	  matchRecord[i]=0xFFFFFFFF;
	}
      }
      if(matchRecord[matchRecordIndex]>currBLit) {
	matchRecord[matchRecordIndex]=currBLit;
      }
      md->nextAlts[currBLit]++;
      currBLit++;
      if(currBLit==matchedLen) { break; }
      md->nextAlts[currBLit]=0;
    } else {
      if(currBLit==0) { return false; }
      currBLit--;
    }

    counter++;
    if(counter==50000) {
      counter=0;
      if(env.timeLimitReached()) {
	throw TimeLimitExceededException();
      }
    }

  }
  if(resolvedLit && matchRecord[1]>=matchedLen) {
    currBLit--;
    goto binding_start;
  }
  return true;
}


struct MatchBtrFn
{
  DECL_RETURN_TYPE(MatchIterator);
  OWN_RETURN_TYPE operator()(Matcher* state, pair<Literal*,Literal*> lp)
  { return state->matches(lp.first, lp.second, false); }
};


bool MLMatcher::canBeMatched(Clause* base, DArray<LiteralList*>& alts)
{
  CALL("MLMatcher::canBeMatched");

  DArray<Literal*> baseOrd(32);
  DArray<LiteralList*> altsOrd(32);
  orderLiterals(*base, alts, baseOrd, altsOrd);

  Matcher matcher;

  MatchIterator sbit=getIteratorBacktrackingOnIterable(&matcher,
	  getMappingArray(
		  pushPairIntoArrays(wrapReferencedArray(baseOrd),
			  wrapReferencedArray(altsOrd)),
		  PushPairIntoRightIterableFn<Literal*,LiteralList*>()),
	  MatchBtrFn());

  return sbit.hasNext();
}


/**
 *
 * @b alts is supposed to be an array of LiteralList* with the same number
 * of elements as @b base.
 */
template<class T, class U>
void MLMatcher::orderLiterals(T& base, U& alts,
	  DArray<Literal*>& baseOrd, DArray<LiteralList*>& altsOrd)
{
  CALL("MLMatcher::orderLiterals");

  unsigned baseLen=base.size();
  //first we order base literals by number of their
  //alternatives (smaller come first)
  static BinaryHeap<int,Int> lengths;
  static DHMap<int, List<unsigned>* > len2lits;
  ASS_EQ(lengths.size(), 0);
  ASS_EQ(len2lits.size(), 0);

  for(unsigned i=0;i<baseLen;i++) {
    unsigned len = LiteralList::length(alts[i]);
    List<unsigned>** plst;
    if(len2lits.getValuePtr(len, plst, 0)) {
      lengths.insert(len);
    }
    List<unsigned>::push(i,*plst);
  }

  baseOrd.ensure(baseLen);
  altsOrd.ensure(baseLen);

  unsigned nextli=0;
  while(lengths.size()) {
    unsigned len=lengths.pop();
    List<unsigned>** plst;
    NEVER(len2lits.getValuePtr(len, plst));
    ASS(*plst);
    while(*plst) {
      unsigned basei=List<unsigned>::pop(*plst);
      baseOrd[nextli]=base[basei];
      altsOrd[nextli++]=alts[basei];
    }
  }
  ASS_EQ(nextli, baseLen);
  len2lits.reset();
}

}
