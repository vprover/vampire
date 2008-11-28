/**
 * @file SLQueryForwardSubsumption.cpp
 * Implements class SLQueryForwardSubsumption.
 */

#include "../Lib/Comparison.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Lib/SkipList.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/MMSubstitution.hpp"
#include "../Indexing/Index.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Saturation/SaturationAlgorithm.hpp"
#include "../Shell/Statistics.hpp"

#include "AtomicClauseForwardSubsumption.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;

void AtomicClauseForwardSubsumption::attach(SaturationAlgorithm* salg)
{
  CALL("SLQueryForwardSubsumption::attach");
  ForwardSimplificationEngine::attach(salg);
  _index=_salg->getIndexManager()->request(SIMPLIFYING_ATOMIC_CLAUSE_SUBST_TREE);
}

void AtomicClauseForwardSubsumption::detach()
{
  CALL("SLQueryForwardSubsumption::detach");
  _index=0;
  _salg->getIndexManager()->release(SIMPLIFYING_ATOMIC_CLAUSE_SUBST_TREE);
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

void AtomicClauseForwardSubsumption::perform(Clause* cl, bool& keep, ClauseIterator& toAdd)
{
  CALL("SLQueryForwardSubsumption::perform");
  toAdd=ClauseIterator::getEmpty();

  unsigned clen=cl->length();

  if(clen==0) {
    keep=true;
    return;
  }

  bool success=false;

  for(unsigned li=0;li<clen;li++) {
    SLQueryResultIterator rit=_index->getGeneralizations((*cl)[li], false);
    if(rit.hasNext()) {
      SLQueryResult res=rit.next();
      ASS(res.clause->length()==1);
      success=true;
      break;
    }
  }

  if(success) {
    env.statistics->forwardSubsumed++;
  }
  keep=!success;
}
