/**
 * @file SLQueryBackwardSubsumption.cpp
 * Implements class SLQueryBackwardSubsumption.
 */


#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Array.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Set.hpp"
#include "Lib/TimeCounter.hpp"
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

#include "SLQueryBackwardSubsumption.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


void SLQueryBackwardSubsumption::attach(SaturationAlgorithm* salg)
{
  CALL("SLQueryBackwardSubsumption::attach");
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

struct ClauseExtractorFn
{
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(const SLQueryResult& res)
  {
    return res.clause;
  }
};

struct ClauseToBwSimplRecordFn
{
  DECL_RETURN_TYPE(BwSimplificationRecord);
  OWN_RETURN_TYPE operator()(Clause* cl)
  {
    return BwSimplificationRecord(cl);
  }
};


struct LitSpec {
  LitSpec() {}
  LitSpec(Clause* cl, Literal* lit)
  : clause(cl), literal(lit) {}
  Clause* clause;
  Literal* literal;

  static Comparison compare(const LitSpec& ls1, const LitSpec& ls2)
  {
    size_t c1id=reinterpret_cast<size_t>(ls1.clause);
    size_t c2id=reinterpret_cast<size_t>(ls2.clause);
    if(c1id!=c2id) {
      return c1id>c2id ? GREATER : LESS;
    }
    size_t l1id=reinterpret_cast<size_t>(ls1.literal);
    size_t l2id=reinterpret_cast<size_t>(ls2.literal);
    return l1id>l2id ? GREATER : (l1id==l2id ? EQUAL : LESS);
  }
  static Comparison compare(Clause* c, const LitSpec& ls2)
  {
    size_t c1id=reinterpret_cast<size_t>(c);
    size_t c2id=reinterpret_cast<size_t>(ls2.clause);
    return c1id>c2id ? GREATER : (c1id==c2id ? EQUAL : LESS);
  }
};

unsigned getTopLevelVars(Term* t)
{
  unsigned res=0;
  TermList* arg=t->args();
  while(arg->isNonEmpty()) {
    if(arg->isVar()) {
      res++;
    }
    arg=arg->next();
  }
  return res;
}

#undef LOGGING
#define LOGGING 0

void SLQueryBackwardSubsumption::perform(Clause* cl,
	BwSimplificationRecordIterator& simplifications)
{
  CALL("SLQueryBackwardSubsumption::perform");
  ASSERT_VALID(*cl);

  //we do all work in this method, so we can just measure time simply
  //(which cannot generally be done when iterators are involved)
  TimeCounter tc(TC_BACKWARD_SUBSUMPTION);

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

  LOGV(*cl);
  static DHSet<Clause*> checkedClauses;
  checkedClauses.reset();

  SLQueryResultIterator rit=_index->getInstances( (*cl)[lmIndex], false, false);
  while(rit.hasNext()) {
    SLQueryResult res=rit.next();
    Clause* icl=res.clause;
    Literal* ilit=res.literal;
    unsigned ilen=icl->length();
    if(ilen<clen || icl==cl) {
      continue;
    }

    if(checkedClauses.contains(icl)) {
      continue;
    }
    checkedClauses.insert(icl);

    RSTAT_CTR_INC("bs candidates");

    LOGV(*icl);

    if(!mustPredInit) {
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
    RSTAT_CTR_INC("bs mustPred survivors");

    //here we check that for every literal header in the base clause
    //there is a literal with the same header in the instance
    if(!basePredsInit) {
      basePredsInit=true;
      basePreds.reset();
//      //since the base clause has at least two children, this will always
//      //contain an existing literal header after the loop
//      mustPred=0;
      for(unsigned bi=0;bi<clen;bi++) {
	if(bi==lmIndex) {
	  continue;
	}
        unsigned pred=(*cl)[bi]->header();
        basePreds.insert(pred);
//        if(pred>mustPred) {
//          mustPred=pred;
//        }
      }
    }
    unsigned allowedMisses=ilen-clen; //how many times the instance may contain a predicate that is not in the base clause
    bool fail=false;
//    bool haveMustPred=false;
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
//      if(pred==mustPred) {
//	haveMustPred=true;
//      }
    }
    if(fail || !haveMustPred) {
      continue;
    }

    RSTAT_CTR_INC("bs survived");



    LiteralList::push(res.literal, matchedLits[lmIndex]);
    for(unsigned bi=0;bi<clen;bi++) {
      for(unsigned ii=0;ii<ilen;ii++) {
	if(bi==lmIndex && (*icl)[ii]==res.literal) {
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

    if(MLMatcher::canBeMatched(cl,icl,matchedLits.array(),0)) {
      ClauseList::push(icl, subsumed);
      env.statistics->backwardSubsumed++;
    }

  match_fail:
    for(unsigned bi=0; bi<clen; bi++) {
      matchedLits[bi]->destroy();
      matchedLits[bi]=0;
    }
  }


  if(subsumed) {
    simplifications=getPersistentIterator(
	    getMappingIterator(ClauseList::Iterator(subsumed), ClauseToBwSimplRecordFn()));
    subsumed->destroy();
  } else {
    simplifications=BwSimplificationRecordIterator::getEmpty();
  }
  return;
}

}
