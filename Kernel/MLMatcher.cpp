/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file MLMatcher.cpp
 * Implements class MLMatcher.
 */

#include <algorithm>

#include "Lib/BinaryHeap.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Hash.hpp"
#include "Lib/TriangularArray.hpp"

#include "Clause.hpp"
#include "Matcher.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "MLMatcher.hpp"

#if VDEBUG
#include <iostream>
#endif


namespace {

using namespace Lib;
using namespace Kernel;


typedef DHMap<unsigned,unsigned, IdentityHash> UUMap;


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

bool createLiteralBindings(Literal* baseLit, LiteralList const* alts, Clause* instCl, Literal* resolvedLit,
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
          // add index of the literal in instance clause at the end of the binding sequence
	  new(altBindingData++) TermList((size_t)instCl->getLiteralPosition(alit));
	}
      }
      if(MatchingUtils::matchReversedArgs(baseLit, alit)) {
	ArrayStoringBinder binder(altBindingData, variablePositions);
	MatchingUtils::matchReversedArgs(baseLit, alit, binder);
	*altBindingPtrs=altBindingData;
	altBindingPtrs++;
	altBindingData+=numVars;
	if(resolvedLit) {
	  new(altBindingData++) TermList((size_t)0);
	} else {
          // add index of the literal in instance clause at the end of the binding sequence
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
        // add index of the literal in instance clause at the end of the binding sequence
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
      MatchingUtils::matchReversedArgs(baseLit, resolvedLit, binder);
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
  LiteralList const* const* alts;
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

  unsigned getRemainingInCurrent(unsigned bi) const
  {
    return remaining->get(bi,bi);
  }

  unsigned getAltRecordIndex(unsigned bi, unsigned alti) const
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
                  unsigned b2Index, unsigned i2AltIndex, pair<int,int>* iinfo) const
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
    CALL("MatchingData::bindAlt");

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
    CALL("MatchingData::getIntersectInfo");

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

  bool isInitialized(unsigned bIndex) const {
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

}  // namespace




namespace Kernel
{

using namespace Lib;


class MLMatcher::Impl final
{
  public:
    CLASS_NAME(MLMatcher::Impl);
    USE_ALLOCATOR(MLMatcher::Impl);

    Impl();
    ~Impl() = default;

    void init(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList const* const* alts, Literal* resolvedLit, bool multiset);
    bool nextMatch();

    void getMatchedAltsBitmap(vvector<bool>& outMatchedBitmap) const;

    void getBindings(vunordered_map<unsigned, TermList>& outBindings) const;

    // Disallow copy and move because the internal implementation still uses pointers to the underlying storage and it seems hard to untangle that.
    Impl(Impl const&) = delete;
    Impl(Impl&&) = delete;
    Impl& operator=(Impl const&) = delete;
    Impl& operator=(Impl&&) = delete;

  private:
    void initMatchingData(Literal** baseLits0, unsigned baseLen, Clause* instance, LiteralList const* const* alts, Literal* resolvedLit);

  private:
    // Backing storage for the pointers in s_matchingData, used and set up in initMatchingData
    DArray<Literal*> s_baseLits;
    DArray<LiteralList const*> s_altsArr;
    DArray<unsigned> s_varCnts;
    DArray<unsigned*> s_boundVarNums;
    DArray<TermList**> s_altPtrs;
    TriangularArray<unsigned> s_remaining;
    TriangularArray<pair<int,int>* > s_intersections;
    DArray<unsigned> s_nextAlts;
    DArray<unsigned> s_boundVarNumData;
    DArray<TermList*> s_altBindingPtrs;
    DArray<TermList> s_altBindingsData;
    DArray<pair<int,int> > s_intersectionData;

    MatchingData s_matchingData;

    // For backtracking support
    DArray<unsigned> s_matchRecord;
    unsigned s_currBLit;
    int s_counter;
    bool s_multiset;
};


MLMatcher::Impl::Impl()
  : s_baseLits(32)
  , s_altsArr(32)
  , s_varCnts(32)
  , s_boundVarNums(32)
  , s_altPtrs(32)
  , s_remaining(32)
  , s_intersections(32)
  , s_nextAlts(32)
  , s_boundVarNumData(64)
  , s_altBindingPtrs(128)
  , s_altBindingsData(256)
  , s_intersectionData(128)
  , s_matchRecord(32)
{ }


void MLMatcher::Impl::initMatchingData(Literal** baseLits0, unsigned baseLen, Clause* instance, LiteralList const* const* alts, Literal* resolvedLit)
{
  CALL("MLMatcher::Impl::initMatchingData");

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

  // Helper function to swap base literals at indices i and j
  auto swapLits = [this] (int i, int j) {
    std::swap(s_baseLits[i], s_baseLits[j]);
    std::swap(s_altsArr[i], s_altsArr[j]);
  };

  // Reorder base literals to try and reduce backtracking
  // Order:
  // 1. base literals with zero alternatives
  // 2. base literals with one alternative
  // 3. from the remaining base literals the one with the most distinct variables
  // 4. the rest
  for(unsigned i=0;i<baseLen;i++) {
    unsigned distVars=s_baseLits[i]->getDistinctVars();

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

    ASS_LE(zeroAlts, singleAlts);
    ASS_LE(singleAlts, i);
    if(currAltCnt==0) {
      if(zeroAlts!=i) {
	if(singleAlts!=zeroAlts) {
          swapLits(singleAlts, zeroAlts);
	}
        swapLits(i, zeroAlts);
	if(mostDistVarsLit==singleAlts) {
	  mostDistVarsLit=i;
	}
      }
      zeroAlts++;
      singleAlts++;
    } else if(currAltCnt==1 && !(resolvedLit && resolvedLit->couldBeInstanceOf(s_baseLits[i], true)) ) {
      if(singleAlts!=i) {
        swapLits(i, singleAlts);
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
    swapLits(mostDistVarsLit, singleAlts);
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
}


void MLMatcher::Impl::init(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList const* const* alts, Literal* resolvedLit, bool multiset)
{
  CALL("MLMatcher::Impl::init");

  if (resolvedLit) {
    // NOTE(JR): I think using resolvedLit together with multiset does not work since there's only two match records in that case.
    // However, I was not able to find a concrete error, so maybe I've missed something.
    ASS(!multiset);
  }

  initMatchingData(baseLits, baseLen, instance, alts, resolvedLit);

  unsigned matchRecordLen = resolvedLit ? 2 : instance->length();
  s_matchRecord.init(matchRecordLen, 0xFFFFFFFF);
  // What is the matchRecord?
  //   Index is retrieved by getAltRecordIndex:  md->getAltRecordIndex(currBLit, md->nextAlts[currBLit])
  //   The index is the position of the alt literal in 'instance'
  //   Value is compared to currBLit, so it should refer to a base literal
  //
  // So from currBLit we get a record index, and the record is a base literal again???
  //
  // Hypothesis:
  //   The match record tracks for each literal of the instance which base literal is matched to it.
  //   This means it is only necessary for multiset matching (because each instance literal can only be used once for matching).
  //   (Except when resolvedLit is set... then there's only two match records??)
  ASS_EQ(s_matchRecord.size(), matchRecordLen);

  s_matchingData.nextAlts[0] = 0;
  s_currBLit = 0;
  s_counter = 0;
  s_multiset = multiset;
}


bool MLMatcher::Impl::nextMatch()
{
  CALL("MLMatcher::Impl::nextMatch");
  MatchingData* const md = &s_matchingData;

  while (true) {
    MatchingData::InitResult ires = md->ensureInit(s_currBLit);
    if (ires != MatchingData::OK) {
      if (ires == MatchingData::MUST_BACKTRACK) {
        s_currBLit--;
        continue;
      } else {
        ASS_EQ(ires, MatchingData::NO_ALTERNATIVE);
        return false;
      }
    }

    unsigned maxAlt = md->getRemainingInCurrent(s_currBLit);
    while (md->nextAlts[s_currBLit] < maxAlt &&
           (
             // Reject the current alternative (i.e., nextAlts[currBLit]) if
             // 1. We are multiset matching and the alt is already matched to a base literal, or
             ( s_multiset && s_matchRecord[md->getAltRecordIndex(s_currBLit, md->nextAlts[s_currBLit])] < s_currBLit )
             // 2. The induced variable bindings would already lead to a conflict for some later base literal
             || !md->bindAlt(s_currBLit, md->nextAlts[s_currBLit])
           )
          ) {
      md->nextAlts[s_currBLit]++;
    }

    if (md->nextAlts[s_currBLit] < maxAlt) {
      // Got a suitable alternative in nextAlt
      unsigned matchRecordIndex=md->getAltRecordIndex(s_currBLit, md->nextAlts[s_currBLit]);
      for (unsigned i = 0; i < s_matchRecord.size(); i++) {
        if (s_matchRecord[i] == s_currBLit) {
          s_matchRecord[i]=0xFFFFFFFF;
        }
      }
      ASS(!s_multiset || s_matchRecord[matchRecordIndex]>s_currBLit);  // when multiset matching, the match record cannot be set already
      if (s_matchRecord[matchRecordIndex]>s_currBLit) {
        s_matchRecord[matchRecordIndex]=s_currBLit;
      }
      md->nextAlts[s_currBLit]++;
      s_currBLit++;
      if(s_currBLit == md->len) {
        if(md->resolvedLit && s_matchRecord[1] >= md->len) {
          s_currBLit--;
          continue;
        }

        s_currBLit--;  // prepare for next round
        return true;
      }
      md->nextAlts[s_currBLit]=0;
    } else {
      // No alt left for currBLit, backtrack
      ASS_GE(md->nextAlts[s_currBLit], maxAlt);
      if(s_currBLit==0) { return false; }
      s_currBLit--;
    }

    s_counter++;
    if(s_counter==50000) {
      s_counter=0;
      if(env.timeLimitReached()) {
        throw TimeLimitExceededException();
      }
    }

  } // while (true)

  ASSERTION_VIOLATION; // unreachable
}


void MLMatcher::Impl::getMatchedAltsBitmap(vvector<bool>& outMatchedBitmap) const
{
  MatchingData const* const md = &s_matchingData;

  // We cannot extract the matched alts if resolvedLit is set
  // because in that case getAltRecordIndex will always return 0 or 1.
  // See createLiteralBindings(), where this value is set up.
  ASS(!md->resolvedLit);

  outMatchedBitmap.clear();
  outMatchedBitmap.resize(md->instance->length(), false);

  for (unsigned bi = 0; bi < md->len; ++bi) {
    unsigned alti = md->nextAlts[bi] - 1;
    unsigned i = md->getAltRecordIndex(bi, alti);
    outMatchedBitmap[i] = true;
  }
  // outMatchedBitmap[i] == true iff instance[i] is matched by some literal of base
}


void MLMatcher::Impl::getBindings(vunordered_map<unsigned, TermList>& outBindings) const
{
  MatchingData const* const md = &s_matchingData;

  // Untested if using this together with resolvedLit works correctly, but it should (please remove this assertion if you can confirm this).
  ASS(!md->resolvedLit);

  ASS(outBindings.empty());

  for (unsigned bi = 0; bi < md->len; ++bi) {
    unsigned alti = md->nextAlts[bi] - 1;
    for (unsigned vi = 0; vi < md->varCnts[bi]; ++vi) {
      // md->altBindings[bi][alti] contains bindings for the variables in b, ordered by the variable index.
      // md->boundVarNums[bi] contains the corresponding variable indices.
      unsigned var = md->boundVarNums[bi][vi];
      TermList trm = md->altBindings[bi][alti][vi];

      DEBUG_CODE(auto res =) outBindings.insert({var, trm});
#if VDEBUG
      auto it = res.first;
      bool inserted = res.second;
      if (!inserted) {
        ASS_EQ(it->second, trm);
      }
#endif
    }
  }
}


MLMatcher::MLMatcher()
  : m_impl{nullptr}
{ }

void MLMatcher::init(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList const* const* alts, Literal* resolvedLit, bool multiset)
{
  if (!m_impl) {
    m_impl = std::make_unique<MLMatcher::Impl>();
  }
  m_impl->init(baseLits, baseLen, instance, alts, resolvedLit, multiset);
}

MLMatcher::~MLMatcher() = default;

bool MLMatcher::nextMatch()
{
  ASS(m_impl);
  return m_impl->nextMatch();
}

void MLMatcher::getMatchedAltsBitmap(vvector<bool>& outMatchedBitmap) const
{
  ASS(m_impl);
  m_impl->getMatchedAltsBitmap(outMatchedBitmap);
}

void MLMatcher::getBindings(vunordered_map<unsigned, TermList>& outBindings) const
{
  ASS(m_impl);
  m_impl->getBindings(outBindings);
}

bool MLMatcher::canBeMatched(Literal** baseLits, unsigned baseLen, Clause* instance, LiteralList const* const* alts, Literal* resolvedLit, bool multiset)
{
  static MLMatcher::Impl matcher;
  matcher.init(baseLits, baseLen, instance, alts, resolvedLit, multiset);
  return matcher.nextMatch();
}



}  // namespace Kernel
