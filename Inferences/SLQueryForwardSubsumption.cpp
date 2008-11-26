/**
 * @file SLQueryForwardSubsumption.cpp
 * Implements class SLQueryForwardSubsumption.
 */

#include "../Lib/VirtualIterator.hpp"
#include "../Lib/SkipList.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/Comparison.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/MMSubstitution.hpp"
#include "../Indexing/Index.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Saturation/SaturationAlgorithm.hpp"
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
  MatchInfo(Clause* cl, Literal* lit) : clause(cl), literal(lit) {}
  Clause* clause;
  Literal* literal;

  static Comparison compare(const MatchInfo& m1, const MatchInfo& m2)
  {
    size_t c1id=reinterpret_cast<size_t>(m1.clause);
    size_t c2id=reinterpret_cast<size_t>(m2.clause);
    if(c1id!=c2id) {
      return c1id>c2id ? GREATER : LESS;
    }
    size_t l1id=reinterpret_cast<size_t>(m1.literal);
    size_t l2id=reinterpret_cast<size_t>(m2.literal);
    return l1id>l2id ? GREATER : (l1id==l2id ? EQUAL : LESS);
  }
  static Comparison compare(Clause* c, const MatchInfo& m2)
  {
    size_t c1id=reinterpret_cast<size_t>(c);
    size_t c2id=reinterpret_cast<size_t>(m2.clause);
    return c1id>c2id ? GREATER : (c1id==c2id ? EQUAL : LESS);
  }
};

typedef SkipList<MatchInfo,MatchInfo> MISkipList;

void SLQueryForwardSubsumption::perform(Clause* cl, bool& keep, ClauseIterator& toAdd)
{
  CALL("SLQueryForwardSubsumption::perform");
  toAdd=ClauseIterator::getEmpty();

  unsigned clen=cl->length();

  if(clen==0) {
    keep=true;
    return;
  }

  bool failed=false;
  DArray<Literal*> lits(clen);
  DArray< MISkipList* > gens(clen);

  for(unsigned li=0;li<clen;li++) {
    lits[li]=(*cl)[li];
    gens[li]=new MISkipList();
  }

  for(unsigned li=0;li<clen;li++) {
    SLQueryResultIterator rit=_index->getGeneralizations(lits[li]);
    while(rit.hasNext()) {
      SLQueryResult res=rit.next();
      if(li==0 || gens[li-1]->find(res.clause)) {
	gens[li]->insert(MatchInfo(res.clause, res.literal));
      }
    }
    if(gens[li]->isEmpty()) {
      failed=true;
      break;
    }
  }

  if(!failed) {
    MISkipList* lastMatches=gens[clen-1];
    MISkipList::Iterator mit(*lastMatches);
    while(mit.hasNext()) {
      MatchInfo minfo=mit.next();
      MMSubstitution matcher;
      ALWAYS(matcher.match(minfo.literal,0, lits[clen-1],1));

      //here we ignore the fact, that more literals from the
      //same clause can match one literal of cl
      for(unsigned li=clen-2;li>=0;li--) {
	MatchInfo minfo2;
	ALWAYS(gens[li]->find(minfo.clause, minfo2));
	if(!matcher.match(minfo.literal,0, lits[clen-1],1)) {
	  failed=true;
	  goto end;
	}
      }
    }
  }

end:
  for(unsigned li=0;li<clen;li++) {
    delete gens[li];
  }
  keep=failed;
}
