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
 * @file EqualityResolution.cpp
 * Implements class EqualityResolution.
 */

#include <utility>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/Stack.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/MismatchHandler.hpp"
#include "Kernel/HOLUnification.hpp"

#include "Saturation/SaturationAlgorithm.hpp"


#include "EqualityResolution.hpp"

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

struct EqualityResolution::IsNegativeEqualityFn
{
  bool operator()(Literal* l)
  { 
    return l->isEquality() && l->isNegative()
#if VHOL
        // no point trying to resolve two terms of functional sort
        // instead, let negExt grow both sides and then resolve...
        // for first part of condition see comments in NegExt and ImitateProject
        && (l->isFlexRigid() || !SortHelper::getEqualityArgumentSort(l).isArrowSort())
#endif
    ; 
  }
};

void EqualityResolution::attach(SaturationAlgorithm* salg)
{
  CALL("EqualityResolution::attach");

  GeneratingInferenceEngine::attach(salg);
}

template<class UnifAlgo>
struct EqualityResolution::ResultFn
{

  template<class...AlgoArgs>
  ResultFn(Clause* cl, bool afterCheck, Ordering* ord, AlgoArgs... args)
      : _afterCheck(afterCheck), _ord(ord), _cl(cl), _cLen(cl->length()),
        _algo(std::move(args)...) {}

  ClauseIterator operator() (Literal* lit)
  {
    CALL("EqualityResolution::ResultFn::operator()");

    ASS(lit->isEquality());
    ASS(lit->isNegative());

    Recycled<RobSubstitutionTL> sub;
    sub->reset();    
    Recycled<ClauseStack> results;

    TermList arg0 = *lit->nthArgument(0);
    TermList arg1 = *lit->nthArgument(1);

    bool check = true;
#if VHOL
    if(env.property->higherOrder()){
      ASS(!lit->isFlexFlex()); // should never select flex flex literals
      unsigned depth = env.options->higherOrderUnifDepth();
      check = check && (depth == 0 || !lit->isFlexRigid());
    }
#endif

    auto substs = _algo.unifiers(arg0, arg1, &*sub, /* no top level constraints */ check);

    while(substs.hasNext()){
      RobSubstitutionTL* sub = substs.next();

      auto constraints = sub->constraints();
      unsigned newLen=_cLen - 1 + constraints->length();

      Clause* res = new(newLen) Clause(newLen, GeneratingInference1(InferenceRule::EQUALITY_RESOLUTION, _cl));

      Literal* litAfter = 0;

      if (_afterCheck && _cl->numSelected() > 1) {
        TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
        litAfter = sub->apply(lit, DEFAULT_BANK);
      }

      unsigned next = 0;
      bool afterCheckFailed = false;
      for(unsigned i=0;i<_cLen;i++) {
        Literal* curr=(*_cl)[i];
        if(curr!=lit) {
          Literal* currAfter = sub->apply(curr, DEFAULT_BANK);

          if (litAfter) {
            TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

            if (i < _cl->numSelected() && _ord->compare(currAfter,litAfter) == Ordering::GREATER) {
              env.statistics->inferencesBlockedForOrderingAftercheck++;
              res->destroy();
              afterCheckFailed = true;
              break;
            }
          }

          (*res)[next++] = currAfter;
        }
      }

      // try next unifier (of course there isn't one in the syntactic first-order case)
      if(afterCheckFailed) continue;

      for (auto l : *constraints) {
        (*res)[next++] = l;
      }
      ASS_EQ(next,newLen);

      env.statistics->equalityResolution++;
      results->push(res);
      // would like to do the below, but exiting higher-order iterator early causes
      // some issue wrelating to celeting the underlying Substitution whilst it is still
      // recording. TODO fix this and add code back in
      //if(res->isEmpty()){
        // derived the empty clause, no need to continue with loop
        //break;
      //}
    }
    return pvi(getUniquePersistentIterator(ClauseStack::Iterator(*results)));
  }
private:
  bool _afterCheck;
  Ordering* _ord;
  Clause* _cl;
  unsigned _cLen;
  UnifAlgo _algo;
};

ClauseIterator EqualityResolution::generateClauses(Clause* premise)
{
  CALL("EqualityResolution::generateClauses");

  static auto uwa                 = env.options->unificationWithAbstraction();
  static bool fixedPointIteration = env.options->unificationWithAbstractionFixedPointIteration();
  static bool usingUwa            = uwa !=Options::UnificationWithAbstraction::OFF;

#if VHOL
  static bool usingHOL = env.property->higherOrder();
#endif

  if(premise->isEmpty()) {
    return ClauseIterator::getEmpty();
  }
  ASS(premise->numSelected()>0);

  auto it1 = premise->getSelectedLiteralIterator();

  auto it2 = getFilteredIterator(it1,IsNegativeEqualityFn());

  bool afterCheck = getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete();
  Ordering* ord = &_salg->getOrdering();

  if(usingUwa){
    return pvi(getMapAndFlattenIterator(it2, 
      ResultFn<AbstractingAlgo>(premise, afterCheck, ord, MismatchHandler(uwa), fixedPointIteration)));
  }

#if VHOL
  if(usingHOL){
    return pvi(getMapAndFlattenIterator(it2, 
      ResultFn<HOLAlgo>        (premise, afterCheck, ord)));
  }
#endif

  return pvi(getMapAndFlattenIterator(it2, 
      ResultFn<RobAlgo>        (premise, afterCheck, ord)));
}

/**
 * @c toResolve must be an negative equality. If it is resolvable,
 * resolve it and return the resulting clause. If it is not resolvable,
 * return 0.
 */
Clause* EqualityResolution::tryResolveEquality(Clause* cl, Literal* toResolve)
{
  CALL("EqualityResolution::tryResolveEquality");
  
  // AYB should template tryResolveEquality function really...
  auto it = ResultFn<RobAlgo>(cl, /* no aftercheck */ false, /* no ordering */ nullptr)(toResolve);

  if(it.hasNext()) return it.next();
  else return 0;
}

}
