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
 * @file BackwardDemodulation.cpp
 * Implements class SLQueryBackwardSubsumption.
 */


#include "Lib/DHMultiset.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/RapidHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/TermIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "BackwardInequalityResolution.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void BackwardInequalityResolution::attach(SaturationAlgorithm* salg)
{
  CALL("BackwardInequalityResolution::attach");
  BackwardSimplificationEngine::attach(salg);
  _index=static_cast<InequalityResolutionNonUnitIndex*>(
	  _salg->getIndexManager()->request(INEQUALITY_RESOLUTION_NON_UNIT_INDEX) );
}

void BackwardInequalityResolution::detach()
{
  CALL("BackwardInequalityResolution::detach");
  _index=0;
  _salg->getIndexManager()->release(INEQUALITY_RESOLUTION_NON_UNIT_INDEX);
  BackwardSimplificationEngine::detach();
}

struct BackwardInequalityResolution::RemovedIsNonzeroFn
{
  bool operator() (BwSimplificationRecord arg)
  {
    return arg.toRemove!=0;
  }
};

struct BackwardInequalityResolution::ResultFn
{
  typedef DHMultiset<Clause*> ClauseSet;

  ResultFn(Clause* cl)
  : _cl(cl)
  {
    ASS_EQ(_cl->length(),1);
    _removed=SmartPtr<ClauseSet>(new ClauseSet());
  }
  /**
   * Return pair of clauses. First clause is being replaced,
   * and the second is the clause, that replaces it. If no
   * replacement should occur, return pair of zeroes.
   */
  BwSimplificationRecord operator() (TermQueryResult qr)
  {
    CALL("BackwardInequalityResolution::ResultFn::operator()");

    if(_cl==qr.clause || _removed->find(qr.clause)) {
      //the retreived clause was already replaced during this
      //backward demodulation
      return BwSimplificationRecord(0);
    }
 
    Literal* queryLit = (*_cl)[0];

    if(!RapidHelper::resolveInequalities(queryLit, qr.literal)){
      return BwSimplificationRecord(0);
    }

    unsigned len=qr.clause->length();
    Clause* res = new(len - 1) Clause(len - 1, 
      SimplifyingInference2(InferenceRule::BACKWARD_INEQUALITY_RESOLUTION, qr.clause, _cl));

    unsigned next=0;
    for(unsigned i=0;i<len;i++) {
      Literal* curr=(*qr.clause)[i];
      if(curr!=qr.literal) {
        (*res)[next++] = curr;
      }
    }
    ASS_EQ(next,len - 1);

    _removed->insert(qr.clause);
    return BwSimplificationRecord(qr.clause,res);
  }
private:
  Clause* _cl;
  SmartPtr<ClauseSet> _removed;
};


void BackwardInequalityResolution::perform(Clause* cl,
	BwSimplificationRecordIterator& simplifications)
{
  CALL("BackwardInequalityResolution::perform");

  if(cl->length()==1) {
    Literal* lit = (*cl)[0];
    auto res = RapidHelper::isIntComparisonLit(lit);
    if(res.isSome()){
      TermList t = res.unwrap();

      BwSimplificationRecordIterator replacementIterator=
      pvi( getFilteredIterator(
        getMappingIterator(_index->getInstances(t, false),
          ResultFn(cl)),
        RemovedIsNonzeroFn()) );

      simplifications=getPersistentIterator(replacementIterator);
      return;
    }
  }

  simplifications=BwSimplificationRecordIterator::getEmpty();
}

}
