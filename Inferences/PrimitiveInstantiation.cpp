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
  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<PrimitiveInstantiationIndex*> (
    _salg->getIndexManager()->request(PRIMITIVE_INSTANTIATION_INDEX) );
}

void PrimitiveInstantiation::detach()
{
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
  
  Clause* operator() (QueryRes<ResultSubstitutionSP, TermWithoutValue> tqr){
    const int QUERY = 0;

    ResultSubstitutionSP subst = tqr.unifier;

    RStack<Literal*> resLits;

    for(Literal* curr : _cl->iterLits()) {
      resLits->push(subst->apply(curr, QUERY));
    }

    env.statistics->primitiveInstantiations++;  
    return Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::PRIMITIVE_INSTANTIATION, _cl));
  }
  
private:
  Clause* _cl;
};

struct PrimitiveInstantiation::ApplicableRewritesFn
{
  ApplicableRewritesFn(PrimitiveInstantiationIndex* index) : _index(index){}
  VirtualIterator<QueryRes<ResultSubstitutionSP, TermWithoutValue>> operator()(Literal* l)
  {
    TermList lhs = *l->nthArgument(0);
    TermList rhs = *l->nthArgument(1);
   
    TypedTermList lhst(lhs, SortHelper::getEqualityArgumentSort(l));
    TypedTermList rhst(rhs, SortHelper::getEqualityArgumentSort(l));

    TermStack args;
    TermList head;

    ApplicativeHelper::getHeadAndArgs(lhs, head, args);
     
    return pvi(_index->getUnifications((head.isVar() ? lhst : rhst)));
  }
private:
  PrimitiveInstantiationIndex* _index;
};

struct PrimitiveInstantiation::PotentialApplicationIters {
  PrimitiveInstantiation& self;

  auto iterAppls(Clause* cl, Literal* lit) {
    return iterItems(lit)
  //filter out literals that are not suitable for narrowing
      .filter(IsInstantiable())
  //pair of literals and possible rewrites that can be applied to literals
      .flatMap(ApplicableRewritesFn(self._index));
  }
};

VirtualIterator<std::tuple<>> PrimitiveInstantiation::lookaheadResultEstimation(SelectedAtom const& selection) {
  return pvi(dropElementType(PotentialApplicationIters{*this}.iterAppls(selection.clause(), selection.literal())));
}

ClauseIterator PrimitiveInstantiation::generateClauses(Clause* premise)
{
  return pvi(premise->getSelectedLiteralIterator()
          .flatMap([=](auto lit) { return PotentialApplicationIters{*this}.iterAppls(premise, lit); })
          .map(ResultFn(premise)));
}

}
