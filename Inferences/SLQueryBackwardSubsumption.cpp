/**
 * @file SLQueryBackwardSubsumption.cpp
 * Implements class SLQueryBackwardSubsumption.
 */


#include "../Lib/VirtualIterator.hpp"
#include "../Lib/BacktrackData.hpp"
#include "../Lib/BinaryHeap.hpp"
#include "../Lib/SkipList.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/List.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/DHMultiset.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/Metaiterators.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/MMSubstitution.hpp"
#include "../Kernel/MLMatcher.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/LiteralIndex.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Lib/Environment.hpp"
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

typedef SkipList<LitSpec,LitSpec> LSList;

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

  static DArray<LSList> matches(32);
  matches.ensure(clen);

  for(unsigned li=0;li<clen;li++) {
    SLQueryResultIterator rit=_index->getInstances( (*cl)[li], false, false);
    while(rit.hasNext()) {
      SLQueryResult res=rit.next();
      unsigned rlen=res.clause->length();
      if( rlen<clen || (li>0 && !matches[li-1].find(res.clause)) ) {
	continue;
      }
      matches[li].insert(LitSpec(res.clause, res.literal));
    }
    if(matches[li].isEmpty()) {
      toRemove=ClauseIterator::getEmpty();
      while(li!=0) {
	matches[--li].makeEmpty();
      }
      return;
    }
  }

  static DArray<LiteralList*> matchedLits(32);

  ClauseList* subsumed=0;

  matchedLits.init(clen, 0);
  while(matches[clen-1].isNonEmpty()) {
    Clause* mcl=matches[clen-1].top().clause;
    for(unsigned li=0;li<clen;li++) {
      while( LitSpec::compare(mcl, matches[li].top())==GREATER ) {
	matches[li].pop();
      }
      ASS(LitSpec::compare(mcl, matches[li].top())==EQUAL);
      while(matches[li].isNonEmpty() && matches[li].top().clause==mcl) {
	LiteralList::push(matches[li].pop().literal, matchedLits[li]);
      }
    }

    if(MLMatcher::canBeMatched(cl,matchedLits)) {
      ClauseList::push(mcl, subsumed);
      env.statistics->backwardSubsumed++;
    }

    for(unsigned li=0; li<clen-1; li++) {
      matchedLits[li]->destroy();
      matchedLits[li]=0;
    }
  }

  for(unsigned li=0; li<clen-1; li++) {
    matches[li].makeEmpty();
  }

  if(subsumed) {
    toRemove=getPersistentIterator<Clause*>(ClauseList::Iterator(subsumed));
    subsumed->destroy();
  } else {
    toRemove=ClauseIterator::getEmpty();
  }
  return;
}
