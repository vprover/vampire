/**
 * @file MLMatcher.cpp
 * Implements class MLMatcher.
 */

#include "../Lib/BacktrackData.hpp"
#include "../Lib/BacktrackIterators.hpp"
#include "../Lib/BinaryHeap.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Stack.hpp"

#include "Clause.hpp"
#include "Term.hpp"
#include "MLMatcher.hpp"
#include "MMSubstitution.hpp"


using namespace Kernel;

#define TRACE_LONG_MATCHING 0

#if TRACE_LONG_MATCHING

#include <iostream>
#include "../Lib/Timer.hpp"
#include "../Test/Output.hpp"
using namespace std;

#endif

class MatchBtrFn
{
public:
  static SubstIterator succ(MMSubstitution* state, Literal* ll)
  {

  }
};

bool MLMatcher::checkForSubsumptionResolution(Clause* base,
	DArray<LiteralList*>& alts, Literal* resolvedInst)
{
  CALL("MLMatcher::checkForSubsumptionResolution");

  unsigned baseLen=base->length();
  MMSubstitution matcher;
  static DArray<Literal*> baseNR(32);	//non-resolved base literals
  static DArray<LiteralList*> altsNR(32);
  baseNR.ensure(baseLen);
  altsNR.ensure(baseLen);
  unsigned nrLen=baseLen;

  //First we try to match the resolvedInst literal on base
  //literals. We should probably do some backtracking here,
  //but it won't probably help in too many cases, and it
  //could slow things down.
  unsigned nri=0;
  for(unsigned bi=0;bi<baseLen;bi++) {
    if( matcher.match((*base)[bi],0,resolvedInst,1,true) ) {
      nrLen--;
    } else if(alts[bi]==0) {
      //No instance literal matches the base literal at index
      //bi, so there is no subsumption.
      return false;
    } else {
      baseNR[nri]=(*base)[bi];
      altsNR[nri]=alts[bi];
      nri++;
    }
  }
  ASS_EQ(nrLen, nri);

  if(nrLen==baseLen) {
    //This method is supposed to be called only after index
    //finds matchable complementary literals, so the case that
    //the instance literal won't match with any base literal
    //should not occur.
    ASSERTION_VIOLATION;
    return false;
  }

  static DArray<Literal*> baseNROrd(32);
  static DArray<LiteralList*> altsNROrd(32);
  baseNROrd.ensure(nrLen);
  altsNROrd.ensure(nrLen);
  orderLiterals(baseNR, nrLen, altsNR, baseNROrd, altsNROrd);

  static Stack<BacktrackData> bdStack(32);
  static DArray<LiteralList*> rem(32); //remaining alternatives

  ASS(bdStack.isEmpty());
  rem.init(nrLen, 0);

  bool success=getMatch(baseNROrd, nrLen, altsNROrd, matcher, rem, bdStack, false);

  while(!bdStack.isEmpty()) {
    bdStack.pop().drop();
  }
  return success;
}

/**
 * Return true iff from each of first @b base->length() lists in @b alts can
 * be selected one literal, such that they altogether match onto respective
 * literals in @b base clause. If a single literal is presented in
 * multiple lists in @b alts, it still can be matched at most once.
 */
bool MLMatcher::canBeMatched(Clause* base, DArray<LiteralList*>& alts)
{
  CALL("MLMatcher::canBeMatched");

  unsigned baseLen=base->length();

  DArray<Literal*> baseOrd(32);
  DArray<LiteralList*> altsOrd(32);
  orderLiterals(*base, baseLen, alts, baseOrd, altsOrd);

#if TRACE_LONG_MATCHING
  Timer tmr;
  tmr.start();
#endif

  static Stack<BacktrackData> bdStack(32);
  static DArray<LiteralList*> rem(32); //remaining alternatives
  MMSubstitution matcher;

  ASS(bdStack.isEmpty());
  rem.init(baseLen, 0);

  bool success=getMatch(baseOrd, baseLen, altsOrd, matcher, rem, bdStack, true);

  while(!bdStack.isEmpty()) {
    bdStack.pop().drop();
  }

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


template<class T>
void MLMatcher::orderLiterals(T& base, unsigned baseLen, DArray<LiteralList*>& alts,
	  DArray<Literal*>& baseOrd, DArray<LiteralList*>& altsOrd)
{
  CALL("MLMatcher::orderLiterals");

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

bool MLMatcher::getMatch(DArray<Literal*>& base, unsigned baseLen,
	DArray<LiteralList*>& alts,
	MMSubstitution& matcher,
	DArray<LiteralList*>& rem,
	Stack<BacktrackData>& bdStack,
	bool multisetMatching)
{
  CALL("MLMatcher::getMatch");

  if(baseLen==0) {
    return true;
  }

  unsigned depth=bdStack.length();

  //This method is supposed to be able to retrieve successive
  //matches, but it was not needed yet.
//  ASS(depth==0 || depth==baseLen);
//  if(depth==baseLen) {
//    depth--;
//    bdStack.pop().backtrack();
//  }
  ASS_EQ(depth,0);
  for(;;) {
    if(rem[depth]==0) {
      rem[depth]=alts[depth];
      ASS(depth<baseLen);
    } else {
      rem[depth]=rem[depth]->tail();
    }

    if(multisetMatching) {
      //check whether one instance literal isn't matched multiple times
      bool repetitive;
      do {
	if(!rem[depth]) {
	  break;
	}
	repetitive=false;
	for(unsigned li=0;li<depth;li++) {
	  if(rem[depth]->head()==rem[li]->head()) {
	    repetitive=true;
	    break;
	  }
	}
	if(repetitive) {
	  //literal is matched multiple times, let's try the next one
	  rem[depth]=rem[depth]->tail();
	}
      } while(repetitive);
    }
    if(!rem[depth]) {
	if(depth) {
	  depth--;
	  bdStack.pop().backtrack();
	  ASS(bdStack.length()==depth);
	  continue;
	} else {
	  return false;
	}
    }
    BacktrackData bData;
    matcher.bdRecord(bData);
    bool matched=matcher.match(base[depth],0,rem[depth]->head(),1, false);
    matcher.bdDone();
    if(matched) {
      depth++;
      bdStack.push(bData);
      if(depth==baseLen) {
	return true;
      }
    } else {
      bData.backtrack();
    }

  }
}
