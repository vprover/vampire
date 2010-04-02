/**
 * @file CTFwSubsAndRes.cpp
 * Implements class CTFwSubsAndRes.
 */


#include "../Indexing/Index.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"


#include "CTFwSubsAndRes.hpp"

namespace Inferences
{
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void CTFwSubsAndRes::attach(SaturationAlgorithm* salg)
{
  CALL("CTFwSubsAndRes::attach");

  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<ClauseSubsumptionIndex*>(
	  _salg->getIndexManager()->request(FW_SUBSUMPTION_CODE_TREE) );
}

void CTFwSubsAndRes::detach()
{
  CALL("CTFwSubsAndRes::detach");

  _index=0;
  _salg->getIndexManager()->release(FW_SUBSUMPTION_CODE_TREE);
  ForwardSimplificationEngine::detach();
}

void CTFwSubsAndRes::perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer)
{
  CALL("CTFwSubsAndRes::perform");

  TimeCounter tc_fs(TC_FORWARD_SUBSUMPTION);

  Clause::requestAux();

  ClauseIterator subsumers=_index->getSubsumingClauses(cl);
  while(subsumers.hasNext()) {
    Clause* premise=subsumers.next();
    if(premise->hasAux()) {
      //we already yielded this clause as a potential subsumer
      continue;
    }
    premise->setAux(0);
    if(simplPerformer->willPerform(premise)) {
      simplPerformer->perform(premise, 0);
      env.statistics->forwardSubsumed++;
      if(!simplPerformer->clauseKept()) {
	goto fin;
      }
    }
  }

fin:
  Clause::releaseAux();
}


}
