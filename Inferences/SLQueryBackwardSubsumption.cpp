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
 * @file SLQueryBackwardSubsumption.cpp
 * Implements class SLQueryBackwardSubsumption.
 */


#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/ColorHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Statistics.hpp"

#include "SLQueryBackwardSubsumption.hpp"

#undef RSTAT_COLLECTION
#define RSTAT_COLLECTION 0

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


void SLQueryBackwardSubsumption::attach(SaturationAlgorithm* salg)
{
  CALL("SLQueryBackwardSubsumption::attach");
  ASS(!_index);

  BackwardSimplificationEngine::attach(salg);
  _index=static_cast<SimplifyingLiteralIndex*>(
	  _salg->getIndexManager()->request(SIMPLIFYING_SUBST_TREE) );
}

void SLQueryBackwardSubsumption::detach()
{
  CALL("SLQueryBackwardSubsumption::detach");
  _index=0;
  _salg->getIndexManager()->release(SIMPLIFYING_SUBST_TREE);
  BackwardSimplificationEngine::detach();
}

struct SLQueryBackwardSubsumption::ClauseExtractorFn
{
  Clause* operator()(const SLQueryResult& res)
  {
    return res.clause;
  }
};

struct SLQueryBackwardSubsumption::ClauseToBwSimplRecordFn
{
  BwSimplificationRecord operator()(Clause* cl)
  {
    return BwSimplificationRecord(cl);
  }
};


void SLQueryBackwardSubsumption::perform(Clause* cl,
	BwSimplificationRecordIterator& simplifications)
{
  CALL("SLQueryBackwardSubsumption::perform");
  ASSERT_VALID(*cl);

  //we do all work in this method, so we can just measure time simply
  //(which cannot generally be done when iterators are involved)
  TimeCounter tc(TC_BACKWARD_SUBSUMPTION);

  simplifications=BwSimplificationRecordIterator::getEmpty();

  unsigned clen=cl->length();

  if(clen==0) {
    SLQueryResultIterator rit=_index->getAll();
    ClauseIterator subsumedClauses=getUniquePersistentIterator(
	    getFilteredIterator(
		    getMappingIterator(rit,ClauseExtractorFn()),
		    getNonequalFn(cl)));
    ASS(subsumedClauses.knowsSize());
    unsigned subsumedCnt=subsumedClauses.size();
    simplifications=pvi( getMappingIterator(
	    subsumedClauses, ClauseToBwSimplRecordFn()) );
    env.statistics->backwardSubsumed+=subsumedCnt;
    return;
  }

  if(clen==1) {
    SLQueryResultIterator rit=_index->getInstances( (*cl)[0], false, false);
    ClauseIterator subsumedClauses=getUniquePersistentIterator(
	    getFilteredIterator(
		    getMappingIterator(rit,ClauseExtractorFn()),
		    getNonequalFn(cl)));
    ASS(subsumedClauses.knowsSize());
    unsigned subsumedCnt=subsumedClauses.size();
    simplifications=pvi( getMappingIterator(
	    subsumedClauses, ClauseToBwSimplRecordFn()) );
    env.statistics->backwardSubsumed+=subsumedCnt;
    RSTAT_CTR_INC_MANY("bs0 unit performed",subsumedCnt);
    return;
  }

  if(_byUnitsOnly) {
    return;
  }

  unsigned lmIndex=0; //least matchable literal index
  unsigned lmVal=(*cl)[0]->weight();
  for(unsigned i=1;i<clen;i++) {
    Literal* curr=(*cl)[i];//-getTopLevelVars((*cl)[i]);
    unsigned currVal=curr->weight();
    if(currVal>lmVal) {
      lmIndex=i;
      lmVal=currVal;
    }
  }

  static DArray<LiteralList*> matchedLits(32);
  matchedLits.init(clen, 0);

  ClauseList* subsumed=0;

  static DHSet<unsigned> basePreds;
  bool basePredsInit=false;
  bool mustPredInit=false;
  unsigned mustPred;

  static DHSet<Clause*> checkedClauses;
  checkedClauses.reset();

  SLQueryResultIterator rit=_index->getInstances( (*cl)[lmIndex], false, false);
  while(rit.hasNext()) {
    SLQueryResult qr=rit.next();
    Clause* icl=qr.clause;
    Literal* ilit=qr.literal;
    unsigned ilen=icl->length();
    if(ilen<clen || icl==cl) {
      continue;
    }

    if(!checkedClauses.insert(icl)) {
      continue;
    }

    RSTAT_CTR_INC("bs1 0 candidates");

    //here we pick one literal header of the base clause and make sure that
    //every instance clause has it
    if(!mustPredInit) {
      //since the base clause has at least two children, this will always
      //contain an existing literal header after the loop
      mustPred=0;
      for(unsigned bi=0;bi<clen;bi++) {
	if(bi==lmIndex) {
	  continue;
	}
        unsigned pred=(*cl)[bi]->header();
        if(pred>mustPred) {
          mustPred=pred;
        }
      }
    }
    bool haveMustPred=false;
    for(unsigned ii=0;ii<ilen;ii++) {
      Literal* l=(*icl)[ii];
      if(l==ilit) {
	continue;
      }
      unsigned pred=l->header();
      if(pred==mustPred) {
	haveMustPred=true;
      }
    }
    if(!haveMustPred) {
      continue;
    }
    RSTAT_CTR_INC("bs1 1 mustPred survivors");

    //here we check that for every literal header in the base clause
    //there is a literal with the same header in the instance
    if(!basePredsInit) {
      basePredsInit=true;
      basePreds.reset();
      for(unsigned bi=0;bi<clen;bi++) {
	if(bi==lmIndex) {
	  continue;
	}
        unsigned pred=(*cl)[bi]->header();
        basePreds.insert(pred);
      }
    }
    unsigned allowedMisses=ilen-clen; //how many times the instance may contain a predicate that is not in the base clause
    bool fail=false;
    for(unsigned ii=0;ii<ilen;ii++) {
      Literal* l=(*icl)[ii];
      if(l==ilit) {
	continue;
      }
      unsigned pred=l->header();
      if(!basePreds.find(pred)) {
	if(allowedMisses==0) {
	  fail=true;
	  break;
	}
	else {
	  allowedMisses--;
	}
      }
    }
    if(fail) {
      continue;
    }

    RSTAT_CTR_INC("bs1 2 survived");



    LiteralList::push(qr.literal, matchedLits[lmIndex]);
    for(unsigned bi=0;bi<clen;bi++) {
      for(unsigned ii=0;ii<ilen;ii++) {
	if(bi==lmIndex && (*icl)[ii]==qr.literal) {
	  continue;
	}
	if(MatchingUtils::match((*cl)[bi],(*icl)[ii],false)) {
	  LiteralList::push((*icl)[ii], matchedLits[bi]);
	}
      }
      if(!matchedLits[bi]) {
	goto match_fail;
      }
    }

    RSTAT_CTR_INC("bs1 3 final check");
    if(MLMatcher::canBeMatched(cl,icl,matchedLits.array(),0)) {
      ClauseList::push(icl, subsumed);
      env.statistics->backwardSubsumed++;
      RSTAT_CTR_INC("bs1 4 performed");
    }

  match_fail:
    for(unsigned bi=0; bi<clen; bi++) {
      LiteralList::destroy(matchedLits[bi]);
      matchedLits[bi]=0;
    }
  }


  if(subsumed) {
    simplifications=getPersistentIterator(
	    getMappingIterator(ClauseList::Iterator(subsumed), ClauseToBwSimplRecordFn()));
    ClauseList::destroy(subsumed);
  }
  return;
}

}
