/**
 * @file MLMatcher.cpp
 * Implements class MLMatcher.
 */

#include <algorithm>

#include "../Lib/BacktrackData.hpp"
#include "../Lib/BacktrackIterators.hpp"
#include "../Lib/BinaryHeap.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Hash.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Metaarrays.hpp"
#include "../Lib/PairUtils.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/TriangularArray.hpp"

#include "Clause.hpp"
#include "Term.hpp"
#include "Matcher.hpp"
#include "MLMatcher.hpp"

#if VDEBUG
#include <iostream>
#include "../Test/Output.hpp"
using namespace std;
#endif

#define TRACE_LONG_MATCHING 0
#if TRACE_LONG_MATCHING
#include "../Lib/Timer.hpp"
#endif

namespace Kernel
{

using namespace Lib;

typedef DHMap<unsigned,unsigned, IdentityHash> UUMap;

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
  static UUMap varPos;
  static BinaryHeap<unsigned,Int> varNums;
  varPos.reset();
  varNums.reset();

  Term::VariableIterator bvit(baseLit);
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
    if(varPos.insert(var,nextPos)) {
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
	ArrayStoringBinder binder(altBindingData, varPos);
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
      if(MatchingUtils::matchTerms(*baseLit->nthArgument(0),*alit->nthArgument(1)) &&
	  MatchingUtils::matchTerms(*baseLit->nthArgument(1),*alit->nthArgument(0))) {
	ArrayStoringBinder binder(altBindingData, varPos);
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
	ArrayStoringBinder binder(altBindingData, varPos);
	ALWAYS(MatchingUtils::matchArgs(baseLit,alit,binder));
      }

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
  }
  if(resolvedLit && resolvedLit->complementaryHeader()==baseLit->header()) {
    if(!baseLit->arity() || MatchingUtils::matchArgs(baseLit,resolvedLit)) {
      if(numVars) {
	ArrayStoringBinder binder(altBindingData, varPos);
	MatchingUtils::matchArgs(baseLit,resolvedLit,binder);
      }
      *altBindingPtrs=altBindingData;
      altBindingPtrs++;
      altBindingData+=numVars;
      new(altBindingData++) TermList((size_t)1);
    }
    if(baseLit->isEquality() &&
	    MatchingUtils::matchTerms(*baseLit->nthArgument(0),*resolvedLit->nthArgument(1)) &&
	    MatchingUtils::matchTerms(*baseLit->nthArgument(1),*resolvedLit->nthArgument(0))) {
      ArrayStoringBinder binder(altBindingData, varPos);
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
  TermList*** altBindings;
  TriangularArray<unsigned>* remaining;
  unsigned* nextAlts;

  Literal** bases;
  LiteralList** alts;
  Clause* instance;
  Literal* resolvedLit;

  unsigned* boundVarNumStorage;
  TermList** altBindingPtrStorage;
  TermList* altBindingStorage;

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

  bool compatible(unsigned b1Index, TermList* i1Bindings,
  	unsigned b2Index, unsigned i2AltIndex) const
  {
    TermList* i2Bindings=altBindings[b2Index][i2AltIndex];
    unsigned* b1vn=boundVarNums[b1Index];
    unsigned* b2vn=boundVarNums[b2Index];
    unsigned* b1vnStop=boundVarNums[b1Index]+varCnts[b1Index];
    unsigned* b2vnStop=boundVarNums[b2Index]+varCnts[b2Index];
    while(true) {
      while(b1vn!=b1vnStop && *b1vn<*b2vn) { b1vn++; i1Bindings++; }
      if(b1vn==b1vnStop) { return true; }
      while(b2vn!=b2vnStop && *b1vn>*b2vn) { b2vn++; i2Bindings++; }
      if(b2vn==b2vnStop) { return true; }
      if(*b1vn==*b2vn) {
        if(*i1Bindings!=*i2Bindings) { return false; }
        b1vn++; i1Bindings++;
        b2vn++; i2Bindings++;
        if(b1vn==b1vnStop || b2vn==b2vnStop) { return true; }
      }
    }
  }

  bool bindAlt(unsigned bIndex, unsigned altIndex)
  {
    TermList* curBindings=altBindings[bIndex][altIndex];
    for(unsigned i=bIndex+1; i<len; i++) {
      if(!isInitialized(i)) {
	break;
      }
      unsigned remAlts=remaining->get(i,bIndex);
      for(unsigned ai=0;ai<remAlts;ai++) {
        if(!compatible(bIndex,curBindings,i,ai)) {
  	remAlts--;
  	std::swap(altBindings[i][ai], altBindings[i][remAlts]);
  	ai--;
        }
      }
      if(remAlts==0) {
        return false;
      }
      remaining->set(i,bIndex+1,remAlts);
    }
    return true;
  }

  bool isInitialized(unsigned bIndex) {
    return boundVarNums[bIndex];
  }

  InitResult ensureInit(unsigned bIndex)
  {
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

      unsigned remAlts;
      for(unsigned pbi=0;pbi<bIndex;pbi++) { //pbi ~ previous base index
        TermList* pbBindings=altBindings[pbi][nextAlts[pbi]-1];
        remAlts=remaining->get(bIndex, pbi);
        for(unsigned ai=0;ai<remAlts;ai++) {
          if(!compatible(pbi,pbBindings,bIndex,ai)) {
            remAlts--;
            std::swap(altBindings[bIndex][ai], altBindings[bIndex][remAlts]);
            ai--;
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

MatchingData* getMatchingData(Literal** baseLits0, unsigned baseLen, Clause* instance, LiteralList** alts,
	Literal* resolvedLit)
{
  static DArray<Literal*> baseLits(32);
  static DArray<LiteralList*> altsArr(32);
  baseLits.initFromArray(baseLen,baseLits0);
  altsArr.initFromArray(baseLen,alts);

  static DArray<unsigned> varCnts(32);
  static DArray<unsigned*> boundVarNums(32);
  static DArray<TermList**> altPtrs(32);
  static TriangularArray<unsigned> remaining(32);
  static DArray<unsigned> nextAlts(32);

  static DArray<unsigned> boundVarNumData(64);
  //Referenced list of an alternative contains binding for each variable of
  //the base literal, and then a record identifying the alternative literal itself.
  static DArray<TermList*> altBindingPtrs(128);
  static DArray<TermList> altBindingsData(256);
  varCnts.ensure(baseLen);
  boundVarNums.init(baseLen,0);
  altPtrs.ensure(baseLen);
  remaining.setSide(baseLen);
  nextAlts.ensure(baseLen);

  unsigned zeroAlts=0;
  unsigned singleAlts=0;
  size_t baseLitVars=0;
  size_t altCnt=0;
  size_t altBindingsCnt=0;
  for(unsigned i=0;i<baseLen;i++) {
//    unsigned distVars=(*base)[i]->distinctVars();
    unsigned distVars=baseLits[i]->vars(); //an upper estimate is enough
    baseLitVars+=distVars;
    unsigned currAltCnt=0;
    LiteralList::Iterator ait(altsArr[i]);
    while(ait.hasNext()) {
      currAltCnt++;
      if(ait.next()->commutative()) {
	currAltCnt++;
      }
    }
    altCnt+=currAltCnt+1;
    altBindingsCnt+=(distVars+1)*(currAltCnt+1);

    if(currAltCnt==0) {
      if(zeroAlts!=i) {
	std::swap(baseLits[i],baseLits[zeroAlts]);
	std::swap(altsArr[i],altsArr[zeroAlts]);
      }
      zeroAlts++;
      singleAlts++;
    } else if(currAltCnt==1) {
      if(singleAlts!=i) {
	std::swap(baseLits[i],baseLits[singleAlts]);
	std::swap(altsArr[i],altsArr[singleAlts]);
      }
      singleAlts++;
    }
  }
  boundVarNumData.ensure(baseLitVars);
  altBindingPtrs.ensure(altCnt);
  altBindingsData.ensure(altBindingsCnt);

  static MatchingData res;
  res.len=baseLen;
  res.varCnts=varCnts.array();
  res.boundVarNums=boundVarNums.array();
  res.altBindings=altPtrs.array();
  res.remaining=&remaining;
  res.nextAlts=nextAlts.array();

  res.bases=baseLits.array();
  res.alts=altsArr.array();
  res.instance=instance;
  res.resolvedLit=resolvedLit;

  res.boundVarNumStorage=boundVarNumData.array();
  res.altBindingPtrStorage=altBindingPtrs.array();
  res.altBindingStorage=altBindingsData.array();

  return &res;
}


/**
 * If @b resolvedLit is 0, multiset matching is performed.
 */
bool MLMatcher::canBeMatched(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList** alts,
	Literal* resolvedLit, bool multiset)
{
  MatchingData* md=getMatchingData(baseLits, baseLen, instance, alts, resolvedLit);
  if(!md) {
    return false;
  }
  unsigned instLen=instance->length();

  static DArray<unsigned> matchRecord(32);
  unsigned matchRecordLen=resolvedLit?2:instLen;
  matchRecord.init(matchRecordLen,0xFFFFFFFF);


  unsigned matchedLen=md->len;

  md->nextAlts[0]=0;
  unsigned currBLit=0;

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


/**
 * Return true iff from each of first @b base->length() lists in @b alts can
 * be selected one literal, such that they altogether match onto respective
 * literals in @b base clause. If a single literal is presented in
 * multiple lists in @b alts, it still can be matched at most once.
 */
bool MLMatcher::canBeMatched(Clause* base, LiteralList** alts)
{
  CALL("MLMatcher::canBeMatched");

  DArray<Literal*> baseOrd(32);
  DArray<LiteralList*> altsOrd(32);
  orderLiterals(*base, alts, baseOrd, altsOrd);

#if TRACE_LONG_MATCHING
  Timer tmr;
  tmr.start();
#endif

  Matcher matcher;

  //TODO: this actually is not the submultiset subsumption!
  MatchIterator sbit=getIteratorBacktrackingOnIterable(&matcher,
	  getMappingArray(
		  pushPairIntoArrays(wrapReferencedArray(baseOrd),
			  wrapReferencedArray(altsOrd)),
		  PushPairIntoRightIterableFn<Literal*,LiteralList*>()),
	  MatchBtrFn());

  bool success=sbit.hasNext();

#if TRACE_LONG_MATCHING
  tmr.stop();
  if(tmr.elapsedMilliseconds()>1000) {
    int nextIndex=0;
    DHMap<Literal*,int> indexes;
    cout<<"\nBase: "<<Test::Output::toString(base)<<"\n\n";
    for(unsigned i=0;i<baseLen;i++) {
      cout<<Test::Output::toString(baseOrd[i])<<"\n---has instances---\n";
      LiteralList* it=altsOrd[i];
      while(it) {
	Literal* ilit=it->head();
	if(indexes.insert(ilit, nextIndex)) {
	  nextIndex++;
	}
	cout<<indexes.get(ilit)<<": "<<Test::Output::toString(ilit)<<"\n";
	it=it->tail();
      }
      cout<<endl;
    }
    cout<<"DONE in "<<tmr.elapsedMilliseconds()<<" ms\n-----------------------------------\n";
  }
#endif

  return success;
}

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
    unsigned len=alts[i]->length();
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
    NEVER(len2lits.getValuePtr(len, plst, 0));
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
