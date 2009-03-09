/**
 * @file MLMatcher.cpp
 * Implements class MLMatcher.
 */

#include "../Lib/BacktrackData.hpp"
#include "../Lib/BacktrackIterators.hpp"
#include "../Lib/BinaryHeap.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Metaarrays.hpp"
#include "../Lib/PairUtils.hpp"
#include "../Lib/Stack.hpp"

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

struct MatchBtrFn
{
  DECL_RETURN_TYPE(MatchIterator);
  OWN_RETURN_TYPE operator()(Matcher* state, pair<Literal*,Literal*> lp)
  { return state->matches(lp.first, lp.second, false); }
};

typedef pair<Stack<Literal*>*, Matcher*> ResMatchState;

struct ResMatchBtrFn
{
  struct OnStackPushingContext
  {
    OnStackPushingContext(Literal* val) : _val(val) {}
    bool enter(ResMatchState& s)
    { s.first->push(_val); return true; }
    void leave(ResMatchState& s)
    {
      ASS_EQ(s.first->top(),_val);
      s.first->pop();
    }
  private:
    Literal* _val;
  };
  DECL_RETURN_TYPE(VirtualIterator<ResMatchState>);
  OWN_RETURN_TYPE operator()(ResMatchState state, pair<Literal*,Literal*> lp)
  {
    MatchIterator matchIter=state.second->matches(lp.first, lp.second, true);
    OnStackPushingContext skippingCtx(lp.first);
    return pvi( getConcatenatedIterator(
	    pushPairIntoRightIterator(
		    make_pair(state.first, matchIter)),
	    getContextualIterator(SingletonIterator<ResMatchState>(state), skippingCtx)
	    ) );
  }
};


bool MLMatcher::checkForSubsumptionResolution(Clause* base,
	LiteralList** alts, Literal* resolvedInst)
{
  CALL("MLMatcher::checkForSubsumptionResolution");

  unsigned baseLen=base->length();
  Matcher matcher0;

  static DArray<Literal*> baseResolvable(32);
  static DArray<LiteralList*> altsResolvable(32);
  static DArray<Literal*> baseNotResolved(32);
  static DArray<LiteralList*> altsNotResolved(32);
  baseResolvable.ensure(baseLen);
  altsResolvable.ensure(baseLen);
  baseNotResolved.ensure(baseLen);
  altsNotResolved.ensure(baseLen);

  unsigned possiblyResolvable=0;
  unsigned notResolvable=0;
  unsigned riComplHdr=resolvedInst->complementaryHeader();
  for(unsigned i=0;i<baseLen;i++) {
    Literal* blit=(*base)[i];
    if(blit->header()==riComplHdr && MatchingUtils::match(blit, resolvedInst, true) ) {
      baseResolvable[possiblyResolvable]=blit;
      altsResolvable[possiblyResolvable++]=alts[i];
    } else {
      baseNotResolved[notResolvable]=blit;
      altsNotResolved[notResolvable++]=alts[i];
    }
  }
  ASS_EQ(possiblyResolvable+notResolvable,baseLen);
  ASS_G(possiblyResolvable,0);

  ALWAYS(baseResolvable.ensure(possiblyResolvable));
  ALWAYS(altsResolvable.ensure(possiblyResolvable));

  Stack<Literal*> nonResolved0(baseLen);

  VirtualIterator<ResMatchState> rmit=getBacktrackingIterator(
	  ResMatchState(&nonResolved0,&matcher0),
	  pushPairIntoLeftArray(wrapReferencedArray(baseResolvable),
		  resolvedInst),
	  ResMatchBtrFn());
  ASS(rmit.hasNext());
  while(rmit.hasNext()) {
    ResMatchState rms=rmit.next();
    Stack<Literal*>* nonResolved=rms.first;
    Matcher* matcher=rms.second;
    unsigned nrLen=nonResolved->length()+notResolvable;

    if(nrLen==baseLen) {
      continue;
    }

    static DArray<Literal*> baseNR(32);	//non-resolved base literals
    static DArray<LiteralList*> altsNR(32);
    ALWAYS(baseNotResolved.ensure(nrLen));
    ALWAYS(altsNotResolved.ensure(nrLen));

    Stack<Literal*>::Iterator nrit(*nonResolved);//non-resolved iterator
    unsigned bi=possiblyResolvable-1;
    unsigned nri=nrLen-1;
    while(nrit.hasNext()) {
      Literal* nrl=nrit.next();
      while(baseResolvable[bi]!=nrl) {
	bi--;
	ASS(bi<baseLen); //actually checking bi>=0, but bi is unsigned...
      }
      baseNotResolved[nri]=nrl;
      altsNotResolved[nri--]=altsResolvable[bi--];
    }
    ASS_EQ(nri,(unsigned)(notResolvable-1));

    static DArray<Literal*> baseNROrd(32);
    static DArray<LiteralList*> altsNROrd(32);
    baseNROrd.ensure(nrLen);
    altsNROrd.ensure(nrLen);
    orderLiterals(baseNotResolved, altsNotResolved, baseNROrd, altsNROrd);

    MatchIterator sbit=getIteratorBacktrackingOnIterable(matcher,
  	  getMappingArray(
  		  pushPairIntoArrays(wrapReferencedArray(baseNROrd),
  			  wrapReferencedArray(altsNROrd)),
  		  PushPairIntoRightIterableFn<Literal*,LiteralList*>()),
  	  MatchBtrFn());

    if(sbit.hasNext())
      return true;
  }
  return false;


}

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
