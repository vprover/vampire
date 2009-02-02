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
#include "../Kernel/EqHelper.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/TermIndex.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"

#include "BackwardDemodulation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void BackwardDemodulation::attach(SaturationAlgorithm* salg)
{
  CALL("BackwardDemodulation::attach");
  BackwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationSubtermIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_SUBTERM_SUBST_TREE) );
}

void BackwardDemodulation::detach()
{
  CALL("BackwardDemodulation::detach");
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_SUBTERM_SUBST_TREE);
  BackwardSimplificationEngine::detach();
}

void BackwardDemodulation::perform(Clause* cl,
	ClauseIterator& toRemove, ClauseIterator& toAdd)
{
  CALL("BackwardDemodulation::perform");
  
  if(cl->length()!=1 || !(*cl)[0]->isEquality() || !(*cl)[0]->isPositive() ) {
    toAdd=ClauseIterator::getEmpty();
    toRemove=ClauseIterator::getEmpty();
    return;
  }
  Literal* lit=(*cl)[0];
  
  
  
  
  return;
}

}
