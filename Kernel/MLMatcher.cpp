/**
 * @file MLMatcher.cpp
 * Implements class MLMatcher.
 */

#include "../Lib/BacktrackData.hpp"
#include "../Lib/BacktrackIterators.hpp"
#include "../Lib/BinaryHeap.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Metaarrays.hpp"
#include "../Lib/Stack.hpp"

#include "Clause.hpp"
#include "Term.hpp"
#include "MLMatcher.hpp"
#include "MMSubstitution.hpp"

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
  DECL_RETURN_TYPE(SubstIterator);
  OWN_RETURN_TYPE operator()(MMSubstitution* state, pair<Literal*,Literal*> lp)
  { return state->matches(lp.first, 1, lp.second, 2, false); }
};

typedef pair<Stack<Literal*>*, MMSubstitution*> ResMatchState;

struct ResMatchBtrFn
{
  struct OnStackPushingContext
  {
    OnStackPushingContext(Literal* val) : _val(val) {}
    void enter(ResMatchState& s)
    { s.first->push(_val); }
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
    SubstIterator matchIter=state.second->matches(lp.first, 1, lp.second, 2, true);
    OnStackPushingContext skippingCtx(lp.first);
    return getConcatenatedIterator(
	    pushPairIntoRightIterator(
		    pair<Stack<Literal*>*,SubstIterator>(state.first, matchIter)),
	    getContextualIterator(SingletonIterator<ResMatchState>(state), skippingCtx)
	    );
  }
};

bool MLMatcher::checkForSubsumptionResolution(Clause* base,
	DArray<LiteralList*>& alts, Literal* resolvedInst)
{
  CALL("MLMatcher::checkForSubsumptionResolution");

  unsigned baseLen=base->length();
  MMSubstitution matcher0;

  Stack<Literal*> nonResolved0(baseLen);

  VirtualIterator<ResMatchState> rmit=getBacktrackingIterator(
	  ResMatchState(&nonResolved0,&matcher0),
	  pushPairIntoLeftArray(wrapReferencedArray(*base),
		  resolvedInst),
	  ResMatchBtrFn());
  ASS(rmit.hasNext());
  while(rmit.hasNext()) {
    ResMatchState rms=rmit.next();
    Stack<Literal*>* nonResolved=rms.first;
    MMSubstitution* matcher=rms.second;
    unsigned nrLen=nonResolved->length();

    if(nrLen==baseLen) {
      continue;
    }

    static DArray<Literal*> baseNR(32);	//non-resolved base literals
    static DArray<LiteralList*> altsNR(32);
    baseNR.ensure(nrLen);
    altsNR.ensure(nrLen);

    Stack<Literal*>::Iterator nrit(*nonResolved);//non-resolved iterator
    unsigned bi=baseLen-1;
    unsigned nri=nrLen-1;
    while(nrit.hasNext()) {
      Literal* nrl=nrit.next();
      while((*base)[bi]!=nrl) {
	bi--;
	ASS(bi<baseLen); //actually checking bi>=0, but bi is unsigned...
      }
      baseNR[nri]=nrl;
      altsNR[nri--]=alts[bi--];
    }
    ASS(nri==(unsigned)-1);

    static DArray<Literal*> baseNROrd(32);
    static DArray<LiteralList*> altsNROrd(32);
    baseNROrd.ensure(nrLen);
    altsNROrd.ensure(nrLen);
    orderLiterals(baseNR, nrLen, altsNR, baseNROrd, altsNROrd);

    SubstIterator sbit=getBacktrackingIterator(matcher,
  	  getMappingArray(
  		  pushPairIntoArrays(wrapReferencedArray(baseNROrd),
  			  wrapReferencedArray(altsNROrd)),
  		  PushPairIntoRightIterableFn<Literal*,LiteralList*>()),
  	  getBacktrackFnForIterableChoicePoint<MMSubstitution*>(MatchBtrFn()));

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

  MMSubstitution matcher;

  SubstIterator sbit=getBacktrackingIterator(&matcher,
	  getMappingArray(
		  pushPairIntoArrays(wrapReferencedArray(baseOrd),
			  wrapReferencedArray(altsOrd)),
		  PushPairIntoRightIterableFn<Literal*,LiteralList*>()),
	  getBacktrackFnForIterableChoicePoint<MMSubstitution*>(MatchBtrFn()));

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

}
