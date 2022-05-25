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
 * @file BackwardSubsumptionResolution.cpp
 * Implements class BackwardSubsumptionResolution.
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

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Statistics.hpp"

#include "ForwardSubsumptionAndResolution.hpp"

#include "BackwardSubsumptionResolution.hpp"

#undef RSTAT_COLLECTION
#define RSTAT_COLLECTION 0

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


void BackwardSubsumptionResolution::attach(SaturationAlgorithm* salg)
{
  CALL("BackwardSubsumptionResolution::attach");
  BackwardSimplificationEngine::attach(salg);
  _index=static_cast<SimplifyingLiteralIndex*>(
	  _salg->getIndexManager()->request(SIMPLIFYING_SUBST_TREE) );
}

void BackwardSubsumptionResolution::detach()
{
  CALL("BackwardSubsumptionResolution::detach");
  _index=0;
  _salg->getIndexManager()->release(SIMPLIFYING_SUBST_TREE);
  BackwardSimplificationEngine::detach();
}

struct BackwardSubsumptionResolution::ClauseExtractorFn
{
  Clause* operator()(const SLQueryResult& res)
  {
    return res.clause;
  }
};

struct BackwardSubsumptionResolution::ClauseToBwSimplRecordFn
{
  BwSimplificationRecord operator()(Clause* cl)
  {
    return BwSimplificationRecord(cl);
  }
};


void BackwardSubsumptionResolution::perform(Clause* cl,
	BwSimplificationRecordIterator& simplifications)
{
  CALL("BackwardSubsumptionResolution::perform");
  ASSERT_VALID(*cl);

  //we do all work in this method, so we can just measure time simply
  //(which cannot generally be done when iterators are involved)
  TimeCounter tc(TC_BACKWARD_SUBSUMPTION_RESOLUTION);

  unsigned clen=cl->length();

  //by default we don't simplify anything
  simplifications=BwSimplificationRecordIterator::getEmpty();

  if(clen==0) {
    return;
  }

  static DHSet<Clause*> checkedClauses;
  checkedClauses.reset();

  if(clen==1) {
    List<BwSimplificationRecord>* simplRes=0;

    SLQueryResultIterator rit=_index->getInstances( (*cl)[0], true, false);
    while(rit.hasNext()) {
      SLQueryResult qr=rit.next();

      if(!checkedClauses.insert(qr.clause)) {
	continue;
      }

      Clause* resCl=ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause(qr.clause, qr.literal, cl);

      List<BwSimplificationRecord>::push(BwSimplificationRecord(qr.clause,resCl), simplRes);
      env.statistics->backwardSubsumptionResolution++;
      RSTAT_CTR_INC("bsr0 performed (units)");
    }
    if(simplRes) {
      simplifications=pvi( List<BwSimplificationRecord>::DestructiveIterator(simplRes) );
    }
    return;
  }
  if(_byUnitsOnly) {
    return;
  }

  unsigned lmIndex=0; //least matchable literal index
  unsigned lmVal=(*cl)[0]->weight();
  for(unsigned i=1;i<clen;i++) {
    Literal* curr=(*cl)[i];
    unsigned currVal=curr->weight();
    if(currVal>lmVal) {
      lmIndex=i;
      lmVal=currVal;
    }
  }
  Literal* lmLit=(*cl)[lmIndex];
  unsigned lmPred=lmLit->functor();
  unsigned lmHeader=lmLit->header();

  static DArray<LiteralList*> matchedLits(32);
  matchedLits.init(clen, 0);

  bool mustPredInit=false;
  unsigned mustPred;
  static DHSet<unsigned> basePreds;
  bool basePredsInit=false;

  List<BwSimplificationRecord>* simplRes=0;

  SLQueryResultIterator rit=_index->getInstances( lmLit, true, false);
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

    RSTAT_CTR_INC("bsr1 0 candidates");

    //here we pick one literal header of the base clause and make sure that
    //every instance clause has it
    if(!mustPredInit) {
      mustPred=lmHeader;
      for(unsigned bi=0;bi<clen;bi++) {
	if(bi==lmIndex) {
	  continue;
	}
        unsigned pred=(*cl)[bi]->header();
        if(pred!=lmHeader && (mustPred==lmHeader || pred>mustPred)) {
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
    RSTAT_CTR_INC("bsr1 1 mustPred survivors");

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

    RSTAT_CTR_INC("bsr1 2 survived");



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

    RSTAT_CTR_INC("bsr1 3 final check");
    if(MLMatcher::canBeMatched(cl,icl,matchedLits.array(),qr.literal)) {
      RSTAT_CTR_INC("bsr1 4 performed");
      Clause* resCl=ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause(qr.clause, qr.literal, cl);
      List<BwSimplificationRecord>::push(BwSimplificationRecord(qr.clause,resCl), simplRes);
      env.statistics->backwardSubsumptionResolution++;      
    }

  match_fail:
    for(unsigned bi=0; bi<clen; bi++) {
      LiteralList::destroy(matchedLits[bi]);
      matchedLits[bi]=0;
    }
  }





  mustPredInit=false;
  basePredsInit=false;

  rit=_index->getInstances( lmLit, false, false);
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

    RSTAT_CTR_INC("bsr2 0 candidates");

    //here we pick one literal functor of the base clause and make sure that
    //every instance clause has it
    //In the previous code we used header, but here we must disregard the literal
    //polarity
    if(!mustPredInit) {
      mustPred=lmPred;
      for(unsigned bi=0;bi<clen;bi++) {
	if(bi==lmIndex) {
	  continue;
	}
        unsigned pred=(*cl)[bi]->functor();
        if(pred!=lmPred && (mustPred==lmPred || pred>mustPred)) {
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
      unsigned pred=l->functor();
      if(pred==mustPred) {
	haveMustPred=true;
      }
    }
    if(!haveMustPred) {
      continue;
    }
    RSTAT_CTR_INC("bsr2 1 mustPred survivors");

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
    bool haveNeg=false; //there is an instance literal complementary to some base literal
    unsigned allowedMisses=1+ilen-clen; //how many times the instance may contain a predicate that is not in the base clause
    bool fail=false;
    for(unsigned ii=0;ii<ilen;ii++) {
      Literal* l=(*icl)[ii];
      if(l==ilit) {
	continue;
      }
      unsigned pred=l->header();
      if(!haveNeg && basePreds.find(pred^1)) {
	haveNeg=true;
      }
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
    if(fail || !haveNeg) {
      continue;
    }

    RSTAT_CTR_INC("bsr2 2 survived");


    Literal* resolvedLit=0;
    for(unsigned bi=0;bi<clen;bi++) {
      for(unsigned ii=0;ii<ilen;ii++) {
	if(bi==lmIndex && (*icl)[ii]==qr.literal) {
	  continue;
	}
	if(MatchingUtils::match((*cl)[bi],(*icl)[ii],true)) {
	  resolvedLit=(*icl)[ii];
	  goto res_lit_found;
	}
      }
    }
    ASS_EQ(resolvedLit,0);
    continue;

  res_lit_found:
    RSTAT_CTR_INC("bsr2 3 have res lit");

    LiteralList::push(qr.literal, matchedLits[lmIndex]);
    for(unsigned bi=0;bi<clen;bi++) {
      for(unsigned ii=0;ii<ilen;ii++) {
	Literal* ilit=(*icl)[ii];
	if( ilit==resolvedLit || (bi==lmIndex && ilit==qr.literal) ) {
	  continue;
	}
	if(MatchingUtils::match((*cl)[bi],ilit,false)) {
	  LiteralList::push(ilit, matchedLits[bi]);
	}
      }
      if(!matchedLits[bi]) {
	goto match_fail2;
      }
    }

    RSTAT_CTR_INC("bsr2 4 final check");
    if(MLMatcher::canBeMatched(cl,icl,matchedLits.array(),resolvedLit)) {
      RSTAT_CTR_INC("bsr2 5 performed");
      Clause* resCl=ForwardSubsumptionAndResolution::generateSubsumptionResolutionClause(qr.clause, resolvedLit, cl);
      List<BwSimplificationRecord>::push(BwSimplificationRecord(qr.clause,resCl), simplRes);
      env.statistics->backwardSubsumptionResolution++;
    }

  match_fail2:
    for(unsigned bi=0; bi<clen; bi++) {
      LiteralList::destroy(matchedLits[bi]);
      matchedLits[bi]=0;
    }
  }





  if(simplRes) {
    simplifications=pvi( List<BwSimplificationRecord>::DestructiveIterator(simplRes) );
  }
  return;
}

}
