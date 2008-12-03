/**
 * @file SLQueryForwardSubsumption.cpp
 * Implements class SLQueryForwardSubsumption.
 */

#include "../Lib/VirtualIterator.hpp"

#include "../Kernel/Clause.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"


#include "AtomicClauseForwardSubsumption.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;

void AtomicClauseForwardSubsumption::attach(SaturationAlgorithm* salg)
{
  CALL("AtomicClauseForwardSubsumption::attach");
  ForwardSimplificationEngine::attach(salg);
  _index=_salg->getIndexManager()->request(SIMPLIFYING_ATOMIC_CLAUSE_SUBST_TREE);
}

void AtomicClauseForwardSubsumption::detach()
{
  CALL("AtomicClauseForwardSubsumption::detach");
  _index=0;
  _salg->getIndexManager()->release(SIMPLIFYING_ATOMIC_CLAUSE_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

void AtomicClauseForwardSubsumption::perform(Clause* cl, bool& keep, ClauseIterator& toAdd)
{
  CALL("AtomicClauseForwardSubsumption::perform");
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
