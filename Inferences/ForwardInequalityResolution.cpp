/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file ForwardDemodulation.cpp
 * Implements class ForwardDemodulation.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/RapidHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "ForwardInequalityResolution.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void ForwardInequalityResolution::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardDemodulation::attach");
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<InequalityResolutionUnitIndex*>(
	  _salg->getIndexManager()->request(INEQUALITY_RESOLUTION_UNIT_INDEX) );
}

void ForwardInequalityResolution::detach()
{
  CALL("ForwardDemodulation::detach");
  _index=0;
  _salg->getIndexManager()->release(INEQUALITY_RESOLUTION_UNIT_INDEX);
  ForwardSimplificationEngine::detach();
}

bool ForwardInequalityResolution::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("ForwardDemodulation::perform");

  unsigned cLen=cl->length();
  for(unsigned li=0;li<cLen;li++) {
    Literal* lit=(*cl)[li];
    auto result = RapidHelper::isIntComparisonLit(lit);
    if(result.isSome()){
      TermList t = result.unwrap();
      auto generalisations = _index->getGeneralizations(t, false);
      while(generalisations.hasNext()){
        auto result = generalisations.next();
        if(RapidHelper::resolveInequalities(lit, result.literal)){

          premises = pvi( getSingletonIterator(result.clause));

          unsigned len=cLen - 1;
          Clause* res = new(len) Clause(len, 
            SimplifyingInference2(InferenceRule::FORWARD_INEQUALITY_RESOLUTION, result.clause, cl));

          unsigned next=0;
          for(unsigned i=0;i<cLen;i++) {
            Literal* curr=(*cl)[i];
            if(curr!=lit) {
              (*res)[next++] = curr;
            }
          }
          replacement = res;
          return true;
        }
      }
    }
  }

  return false;
}


}