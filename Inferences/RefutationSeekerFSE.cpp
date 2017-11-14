
/*
 * File RefutationSeekerFSE.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file RefutationSeekerFSE.cpp
 * Implements class RefutationSeekerFSE.
 */


#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Int.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"


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
  _index=static_cast<UnitClauseLiteralIndex*>(
	  _salg->getIndexManager()->request(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE) );
}

void RefutationSeekerFSE::detach()
{
  CALL("SLQueryForwardSubsumption::detach");
  _index=0;
  _salg->getIndexManager()->release(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

void RefutationSeekerFSE::perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer)
{
  CALL("RefutationSeekerFSE::perform");

  if(cl->length()!=1) {
    return;
  }

  SLQueryResultIterator rit=_index->getUnifications((*cl)[0], true, false);
  while(rit.hasNext()) {
    SLQueryResult res=rit.next();
    ASS(res.clause->length()==1);

    if(!ColorHelper::compatible(cl->color(), res.clause->color())) {
      continue;
    }

    Inference* inf = new Inference2(Inference::RESOLUTION, cl, res.clause);
    Unit::InputType inpType = (Unit::InputType)
    	Int::max(cl->inputType(), res.clause->inputType());

    Clause* refutation = new(0) Clause(0, inpType, inf);
    refutation->setAge(cl->age());
    env.statistics->resolution++;

    simplPerformer->perform(res.clause, refutation);
    return;
  }
}
