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
 * @file EqualityFactoring.cpp
 * Implements class EqualityFactoring.
 */

#include <utility>

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Statistics.hpp"

#include "EqualityFactoring.hpp"

#include "Indexing/SubstitutionTree.hpp"

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

struct EqualityFactoring::IsPositiveEqualityFn
{
  bool operator()(Literal* l)
  { return l->isEquality() && l->isPositive(); }
};
struct EqualityFactoring::IsDifferentPositiveEqualityFn
{
  IsDifferentPositiveEqualityFn(Literal* lit) : _lit(lit) {}
  bool operator()(Literal* l2)
  { return l2->isEquality() && l2->polarity() && l2!=_lit; }
private:
  Literal* _lit;
};

struct EqualityFactoring::FactorablePairsFn
{
  FactorablePairsFn(Clause* cl) : _cl(cl) {}
  VirtualIterator<pair<pair<Literal*,TermList>,pair<Literal*,TermList> > > operator() (pair<Literal*,TermList> arg)
  {
    auto it1 = getContentIterator(*_cl);

    auto it2 = getFilteredIterator(it1,IsDifferentPositiveEqualityFn(arg.first));

    auto it3 = getMapAndFlattenIterator(it2,EqHelper::EqualityArgumentIteratorFn());

    auto it4 = pushPairIntoRightIterator(arg,it3);

    return pvi( it4 );
  }
private:
  Clause* _cl;
};

void EqualityFactoring::attach(SaturationAlgorithm* salg)
{
  CALL("EqualityFactoring::attach");

  GeneratingInferenceEngine::attach(salg);
}

template<class UnifAlgo>
struct EqualityFactoring::ResultFn
{

  ResultFn(Clause* cl, bool afterCheck, Ordering& ordering)
      : _cl(cl), _cLen(cl->length()), _afterCheck(afterCheck), _ordering(ordering),
        _algo()  {}

  ClauseIterator operator() (pair<pair<Literal*,TermList>,pair<Literal*,TermList> > arg)
  {
    CALL("EqualityFactoring::ResultFn::operator()");

    Literal* sLit=arg.first.first;  // selected literal ( = factored-out literal )
    Literal* fLit=arg.second.first; // fairly boring side literal
    ASS(sLit->isEquality());
    ASS(fLit->isEquality());


    TermList srt = SortHelper::getEqualityArgumentSort(sLit);

    Recycled<RobSubstitutionTL> subst;
    subst->reset();

    if (!subst->unify(srt, SortHelper::getEqualityArgumentSort(fLit))) {
      return ClauseIterator::getEmpty();
    }

    Recycled<ClauseStack> results;

    TermList srtS = subst->apply(srt,DEFAULT_BANK);

    TermList sLHS=arg.first.second;
    TermList sRHS=EqHelper::getOtherEqualitySide(sLit, sLHS);
    TermList fLHS=arg.second.second;
    TermList fRHS=EqHelper::getOtherEqualitySide(fLit, fLHS);
    ASS_NEQ(sLit, fLit);
  
    auto unifiers = _algo.unifiers(sLHS,fLHS, &*subst);

    while(unifiers.hasNext()){
      RobSubstitutionTL* subst = unifiers.next();

      TermList sLHSS = subst->apply(sLHS,DEFAULT_BANK);
      TermList sRHSS = subst->apply(sRHS,DEFAULT_BANK);

      if(Ordering::isGorGEorE(_ordering.compare(sRHSS,sLHSS))) {
        // try next unifier (of course there isn't one in the syntactic first-order case)
        continue;
      }
      TermList fRHSS = subst->apply(fRHS,DEFAULT_BANK);
      if(Ordering::isGorGEorE(_ordering.compare(fRHSS,sLHSS))) {
        continue;
      }
      auto constraints = subst->constraints();
      unsigned newLen=_cLen + constraints->length();

      Clause* res = new(newLen) Clause(newLen, GeneratingInference1(InferenceRule::EQUALITY_FACTORING, _cl));

      (*res)[0]=Literal::createEquality(false, sRHSS, fRHSS, srtS);

      Literal* sLitAfter = 0;
      if (_afterCheck && _cl->numSelected() > 1) {
        TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
        sLitAfter = subst->apply(sLit, DEFAULT_BANK);
      }

      unsigned next = 1;
      bool afterCheckFailed = false;
      for(unsigned i=0;i<_cLen;i++) {
        Literal* curr=(*_cl)[i];
        if(curr!=sLit) {
          Literal* currAfter = subst->apply(curr, DEFAULT_BANK);

          if (sLitAfter) {
            TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
            if (i < _cl->numSelected() && _ordering.compare(currAfter,sLitAfter) == Ordering::GREATER) {
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

      for(Literal* c : *constraints){
        (*res)[next++] = c;
      }
      ASS_EQ(next,newLen);

      env.statistics->equalityFactoring++;
      results->push(res);
    }
    return pvi(getUniquePersistentIterator(ClauseStack::Iterator(*results)));    
  }
private:
  Clause* _cl;
  unsigned _cLen;
  bool _afterCheck;
  Ordering& _ordering;
  UnifAlgo _algo;
};

ClauseIterator EqualityFactoring::generateClauses(Clause* premise)
{
  CALL("EqualityFactoring::generateClauses");

  if(premise->length()<=1) {
    return ClauseIterator::getEmpty();
  }
  ASS(premise->numSelected()>0);

  auto it1 = premise->getSelectedLiteralIterator();

  auto it2 = getFilteredIterator(it1,IsPositiveEqualityFn());

  auto it3 = getMapAndFlattenIterator(it2,EqHelper::LHSIteratorFn(_salg->getOrdering()));

  auto it4 = getMapAndFlattenIterator(it3,FactorablePairsFn(premise));

  bool afterCheck = getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete();
  Ordering& ord = _salg->getOrdering();

#if VHOL
  if(env.property->higherOrder()){
    return pvi(getMapAndFlattenIterator(it4, ResultFn<HOLAlgo>(premise, afterCheck, ord)));
  }
#endif

  return   pvi(getMapAndFlattenIterator(it4, ResultFn<RobAlgo>(premise, afterCheck, ord)));
}

}
