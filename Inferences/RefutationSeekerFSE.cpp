/**
 * @file RefutationSeekerFSE.cpp
 * Implements class RefutationSeekerFSE.
 */


#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/Int.hpp"

#include "../Kernel/Unit.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Clause.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/LiteralIndex.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"


#include "RefutationSeekerFSE.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;

void RefutationSeekerFSE::attach(SaturationAlgorithm* salg)
{
  CALL("SLQueryForwardSubsumption::attach");
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<UnitClauseSimplifyingLiteralIndex*>(
	  _salg->getIndexManager()->request(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE) );
}

void RefutationSeekerFSE::detach()
{
  CALL("SLQueryForwardSubsumption::detach");
  _index=0;
  _salg->getIndexManager()->release(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

void RefutationSeekerFSE::perform(Clause* cl, bool& keep, ClauseIterator& toAdd,
	ClauseIterator& premises)
{
  CALL("RefutationSeekerFSE::perform");

  toAdd=ClauseIterator::getEmpty();
  premises=ClauseIterator::getEmpty();
  keep=true;

  if(cl->length()!=1) {
    return;
  }

  SLQueryResultIterator rit=_index->getUnifications((*cl)[0], true, false);
  if(rit.hasNext()) {
    SLQueryResult res=rit.next();
    ASS(res.clause->length()==1);

    Inference* inf = new Inference2(Inference::RESOLUTION, cl, res.clause);
    Unit::InputType inpType = (Unit::InputType)
    	Int::max(cl->inputType(), res.clause->inputType());

    Clause* refutation = new(0) Clause(0, inpType, inf);
    refutation->setAge(Int::max(cl->age(),res.clause->age())+1);
    env.statistics->resolution++;

    toAdd=pvi( getSingletonIterator(refutation) );
    premises=pvi( getSingletonIterator(res.clause) );
    keep=false;
  }
}
