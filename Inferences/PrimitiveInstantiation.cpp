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
 * @file PrimitiveInstantiation.cpp
 * Implements class PrimitiveInstantiation.
 */

#include "Debug/RuntimeStatistics.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "PrimitiveInstantiation.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

namespace Inferences
{
  
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void PrimitiveInstantiation::attach(SaturationAlgorithm* salg)
{
  CALL("PrimitiveInstantiation::attach");

  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<PrimitiveInstantiationIndex*> (
    _salg->getIndexManager()->request(PRIMITIVE_INSTANTIATION_INDEX) );
}

void PrimitiveInstantiation::detach()
{
  CALL("PrimitiveInstantiation::detach");

  _index=0;
  _salg->getIndexManager()->release(PRIMITIVE_INSTANTIATION_INDEX);
  GeneratingInferenceEngine::detach();
}

struct PrimitiveInstantiation::IsInstantiable
{
  bool operator()(Literal* l)
  { 
    if(SortHelper::getEqualityArgumentSort(l) != AtomicSort::boolSort()){
      return false;
    }
    
    TermList lhs = *(l->nthArgument(0));
    TermList rhs = *(l->nthArgument(1));
    
    TermList head;
    TermStack args;
    ApplicativeHelper::getHeadAndArgs(lhs, head, args);
    if(head.isVar()){ return true; }
    ApplicativeHelper::getHeadAndArgs(rhs, head, args);
    if(head.isVar()){ return true; }

    return false; 
  }
};

struct PrimitiveInstantiation::ResultFn
{
  ResultFn(Clause* cl): _cl(cl){}
  
  Clause* operator() (TermQueryResult tqr){
    const int QUERY = 0;

    ResultSubstitutionSP subst = tqr.substitution;

    unsigned cLen = _cl->length(); 
   
    Clause* res = new(cLen) Clause(cLen, GeneratingInference1(InferenceRule::PRIMITIVE_INSTANTIATION, _cl));

    for(unsigned i=0;i<cLen;i++) {
      Literal* curr=(*_cl)[i];
      Literal* currAfter = subst->apply(curr, QUERY);
      (*res)[i] = currAfter;
    }

    env.statistics->primitiveInstantiations++;  
    return res;
  }
  
private:
  Clause* _cl;
};

struct PrimitiveInstantiation::ApplicableRewritesFn
{
  
  ApplicableRewritesFn(PrimitiveInstantiationIndex* index) : _index(index){}
  VirtualIterator<TermQueryResult> operator()(Literal* l)
  {
    CALL("PrimitiveInstantiation::ApplicableRewritesFn()");
        
    TermList lhs = *l->nthArgument(0);
    TermList rhs = *l->nthArgument(1);
   
    TermStack args;
    TermList head;

    ApplicativeHelper::getHeadAndArgs(lhs, head, args);
     
    return pvi(_index->getUnifications((head.isVar() ? lhs : rhs)));
  }
private:
  PrimitiveInstantiationIndex* _index;
};

ClauseIterator PrimitiveInstantiation::generateClauses(Clause* premise)
{
  CALL("PrimitiveInstantiation::generateClauses");
  
  //is this correct?
  auto it1 = premise->getSelectedLiteralIterator();
  //filter out literals that are not suitable for narrowing
  auto it2 = getFilteredIterator(it1, IsInstantiable());

  //pair of literals and possible rewrites that can be applied to literals
  auto it3 = getMapAndFlattenIterator(it2, ApplicableRewritesFn(_index));
  
  //apply rewrite rules to literals
  auto it4 = getMappingIterator(it3, ResultFn(premise));
  

  return pvi( it4 );

}

}
