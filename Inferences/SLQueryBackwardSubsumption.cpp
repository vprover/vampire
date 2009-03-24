/**
 * @file SLQueryBackwardSubsumption.cpp
 * Implements class SLQueryBackwardSubsumption.
 */


#include "../Lib/Comparison.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Set.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Matcher.hpp"
#include "../Kernel/MLMatcher.hpp"
#include "../Kernel/Term.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/LiteralIndex.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Shell/Statistics.hpp"

#include "SLQueryBackwardSubsumption.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;

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

struct ResultClauseExtractor
{
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(const SLQueryResult& res)
  {
    return res.clause;
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

void SLQueryBackwardSubsumption::perform(Clause* cl,
	ClauseIterator& toRemove, ClauseIterator& toAdd)
{
  CALL("SLQueryBackwardSubsumption::perform");

  toAdd=ClauseIterator::getEmpty();
  unsigned clen=cl->length();

  if(clen==1) {
    SLQueryResultIterator rit=_index->getInstances( (*cl)[0], false, false);
    toRemove=getUniquePersistentIterator(
	    getMappingIterator(rit,ResultClauseExtractor()) );
    ASS(toRemove.knowsSize());
    env.statistics->backwardSubsumed+=toRemove.size();
    return;
  }

  unsigned lmIndex=0; //least matchable literal index
  unsigned lmVal=(*cl)[0]->weight();
  for(unsigned i=0;i<clen;i++) {
    Literal* curr=(*cl)[i];
    unsigned currVal=curr->weight();
    if(currVal>lmVal) {
      lmIndex=i;
      lmVal=currVal;
    }
  }

  static DArray<LiteralList*> matchedLits(32);
  matchedLits.init(clen, 0);

  ClauseList* subsumed=0;

  Set<Clause*> checkedClauses;
  SLQueryResultIterator rit=_index->getInstances( (*cl)[lmIndex], false, false);
  while(rit.hasNext()) {
    SLQueryResult res=rit.next();
    Clause* icl=res.clause;
    unsigned ilen=icl->length();
    if( ilen<clen ) {
	continue;
    }

    if(checkedClauses.contains(icl)) {
      continue;
    }
    checkedClauses.insert(icl);

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
    toRemove=getPersistentIterator(ClauseList::Iterator(subsumed));
    subsumed->destroy();
  } else {
    toRemove=ClauseIterator::getEmpty();
  }
  return;
}
