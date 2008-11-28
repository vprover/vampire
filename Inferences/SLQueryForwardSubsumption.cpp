/**
 * @file SLQueryForwardSubsumption.cpp
 * Implements class SLQueryForwardSubsumption.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Lib/BinaryHeap.hpp"
#include "../Lib/SkipList.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/List.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/DHMultiset.hpp"
#include "../Lib/Comparison.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/MMSubstitution.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Shell/Statistics.hpp"

#include "SLQueryForwardSubsumption.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;

void SLQueryForwardSubsumption::attach(SaturationAlgorithm* salg)
{
  CALL("SLQueryForwardSubsumption::attach");
  ForwardSimplificationEngine::attach(salg);
  _index=_salg->getIndexManager()->request(SIMPLIFYING_SUBST_TREE);
}

void SLQueryForwardSubsumption::detach()
{
  CALL("SLQueryForwardSubsumption::detach");
  _index=0;
  _salg->getIndexManager()->release(SIMPLIFYING_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

struct MatchInfo {
  MatchInfo() {}
  MatchInfo(Clause* cl, Literal* cLit, Literal* qLit)
  : clause(cl), clauseLiteral(cLit), queryLiteral(qLit) {}
  Clause* clause;
  Literal* clauseLiteral;
  Literal* queryLiteral;

  static Comparison compare(const MatchInfo& m1, const MatchInfo& m2)
  {
    size_t c1id=reinterpret_cast<size_t>(m1.clause);
    size_t c2id=reinterpret_cast<size_t>(m2.clause);
    if(c1id!=c2id) {
      return c1id>c2id ? GREATER : LESS;
    }
    size_t cl1id=reinterpret_cast<size_t>(m1.clauseLiteral);
    size_t cl2id=reinterpret_cast<size_t>(m2.clauseLiteral);
    if(cl1id!=cl2id) {
      return cl1id>cl2id ? GREATER : LESS;
    }
    size_t ql1id=reinterpret_cast<size_t>(m1.queryLiteral);
    size_t ql2id=reinterpret_cast<size_t>(m2.queryLiteral);
    return ql1id>ql2id ? GREATER : (ql1id==ql2id ? EQUAL : LESS);
  }
  static Comparison compare(Clause* c, const MatchInfo& m2)
  {
    size_t c1id=reinterpret_cast<size_t>(c);
    size_t c2id=reinterpret_cast<size_t>(m2.clause);
    return c1id>c2id ? GREATER : (c1id==c2id ? EQUAL : LESS);
  }
};

struct PtrHash {
  static unsigned hash(void* ptr) {
    return static_cast<unsigned>(reinterpret_cast<size_t&>(ptr)>>4);
  }
};
struct PtrHash2 {
  static unsigned hash(void* ptr) {
    return static_cast<unsigned>(reinterpret_cast<size_t&>(ptr)>>3);
  }
};

//typedef BinaryHeap<MatchInfo,MatchInfo> MISkipList;
typedef SkipList<MatchInfo,MatchInfo> MISkipList;
typedef List<Literal*> LiteralList;
typedef DHMap<Literal*, List<Literal*>* > MatchMap;

void SLQueryForwardSubsumption::perform(Clause* cl, bool& keep, ClauseIterator& toAdd)
{
  CALL("SLQueryForwardSubsumption::perform");
  toAdd=ClauseIterator::getEmpty();

  unsigned clen=cl->length();
  if(clen==0) {
    keep=true;
    return;
  }

  MISkipList gens;
  DHMultiset<Clause*,PtrHash,PtrHash2> genCounter;
//  DHMultiset<Clause*,PtrHash> genCounter;

  for(unsigned li=0;li<clen;li++) {
    SLQueryResultIterator rit=_index->getGeneralizations( (*cl)[li], false);
    while(rit.hasNext()) {
      SLQueryResult res=rit.next();
      unsigned rlen=res.clause->length();
      if(rlen==1) {
	env.statistics->forwardSubsumed++;
	keep=false;
	return;
      } else if(rlen>clen) {
	continue;
      }
      genCounter.insert(res.clause);
      gens.insert(MatchInfo(res.clause, res.literal, (*cl)[li] ));
    }
  }

  if(gens.isEmpty()) {
    keep=true;
    return;
  }

  bool finished=false;

  static DArray<List<Literal*>*> matches(16);

  MatchInfo mi=gens.pop();
  do {
    Clause* mcl=mi.clause;
    unsigned mlen=mi.clause->length();
    if(mlen>genCounter.multiplicity(mi.clause)) {
      do {
	if(gens.isEmpty()) {
	  finished=true;
	  break;
	}
	mi=gens.pop();
      } while(mi.clause==mcl);
      continue;
    }
    MatchMap matchMap;

    do {
      LiteralList** alts; //pointer to list of possibly matching literals of cl
      matchMap.setPosition(mi.clauseLiteral, alts, 0);
      LiteralList::push(mi.queryLiteral, *alts);

      if(gens.isEmpty()) {
	finished=true;
      } else {
	mi=gens.pop();
      }
    } while(mi.clause==mcl && !finished);

    matches.ensure(mlen);
    bool mclMatchFailed=false;
    for(unsigned li=0;li<mlen;li++) {
      LiteralList* alts;
      if(matchMap.find( (*mcl)[li], alts) ) {
	ASS(alts);
	matches[li]=alts;
      } else {
	mclMatchFailed=true;
	break;
      }
    }

    if(!mclMatchFailed) {
      MMSubstitution matcher;
      for(unsigned li=0;li<mlen;li++) {
	if(!matcher.match( (*mcl)[li],0, matches[li]->head(),1 )) {
	  mclMatchFailed=true;
	  break;
	}
      }
    }

    MatchMap::Iterator mmit(matchMap);
    while(mmit.hasNext()) {
      mmit.next()->destroy();
    }

    if(!mclMatchFailed) {
      env.statistics->forwardSubsumed++;
      keep=false;
      return;
    }

  } while(!finished);

  keep=true;
}
