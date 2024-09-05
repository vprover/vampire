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

#include "Shell/ConditionalRedundancyHandler.hpp"
#include "Shell/Statistics.hpp"

#include "EqualityFactoring.hpp"

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
using std::pair;

EqualityFactoring::EqualityFactoring()
  : _abstractionOracle(AbstractionOracle::createOnlyHigherOrder())
  , _uwaFixedPointIteration(env.options->unificationWithAbstractionFixedPointIteration())
{

}

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
    auto it1 = _cl->iterLits();

    auto it2 = getFilteredIterator(it1,IsDifferentPositiveEqualityFn(arg.first));

    auto it3 = getMapAndFlattenIterator(it2,EqHelper::EqualityArgumentIteratorFn());

    auto it4 = pushPairIntoRightIterator(arg,it3);

    return pvi( it4 );
  }
private:
  Clause* _cl;
};

struct EqualityFactoring::ResultFn
{
  ResultFn(EqualityFactoring& self, Clause* cl, bool afterCheck, const ConditionalRedundancyHandler& condRedHandler, Ordering& ordering, bool fixedPointIteration)
      : _self(self), _cl(cl), _cLen(cl->length()), _afterCheck(afterCheck), _condRedHandler(condRedHandler), _ordering(ordering), _fixedPointIteration(fixedPointIteration) {}
  Clause* operator() (pair<pair<Literal*,TermList>,pair<Literal*,TermList> > arg)
  {
    auto absUnif = AbstractingUnifier::empty(_self._abstractionOracle);
    Literal* sLit=arg.first.first;  // selected literal ( = factored-out literal )
    Literal* fLit=arg.second.first; // fairly boring side literal
    ASS(sLit->isEquality());
    ASS(fLit->isEquality());


    TermList srt = SortHelper::getEqualityArgumentSort(sLit);

    if (!absUnif.unify(srt, 0, SortHelper::getEqualityArgumentSort(fLit), 0)) {
      return 0;
    }


    TermList sLHS=arg.first.second;
    TermList sRHS=EqHelper::getOtherEqualitySide(sLit, sLHS);
    TermList fLHS=arg.second.second;
    TermList fRHS=EqHelper::getOtherEqualitySide(fLit, fLHS);
    ASS_NEQ(sLit, fLit);

    if(!absUnif.unify(sLHS,0,fLHS,0)) {
      return 0;
    }

    if (_fixedPointIteration && !absUnif.fixedPointIteration()) {
      return nullptr;
    }

    TermList srtS = absUnif.subs().apply(srt,0);
    TermList sLHSS = absUnif.subs().apply(sLHS,0);
    TermList sRHSS = absUnif.subs().apply(sRHS,0);
    if(Ordering::isGreaterOrEqual(_ordering.compare(sRHSS,sLHSS))) {
      return 0;
    }
    TermList fRHSS = absUnif.subs().apply(fRHS,0);
    if(Ordering::isGreaterOrEqual(_ordering.compare(fRHSS,sLHSS))) {
      return 0;
    }
    auto constraints = absUnif.computeConstraintLiterals();

    RStack<Literal*> resLits;

    resLits->push(Literal::createEquality(false, sRHSS, fRHSS, srtS));

    Literal* sLitAfter = 0;
    if (_afterCheck && _cl->numSelected() > 1) {
      TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
      sLitAfter = absUnif.subs().apply(sLit, 0);
    }

    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=sLit) {
        Literal* currAfter = absUnif.subs().apply(curr, 0);

        if (sLitAfter) {
          TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
          if (i < _cl->numSelected() && _ordering.compare(currAfter,sLitAfter) == Ordering::GREATER) {
            env.statistics->inferencesBlockedForOrderingAftercheck++;
            return nullptr;
          }
        }

        resLits->push(currAfter);
      }
    }

    if (!absUnif.usesUwa()) {
      if (!_condRedHandler.handleReductiveUnaryInference(_cl, &absUnif.subs())) {
        env.statistics->skippedEqualityFactoring++;
        return nullptr;
      }
    }

    resLits->loadFromIterator(constraints->iterFifo());

    env.statistics->equalityFactoring++;

    return Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::EQUALITY_FACTORING, _cl));
  }
private:
  EqualityFactoring& _self;
  Clause* _cl;
  unsigned _cLen;
  bool _afterCheck;
  const ConditionalRedundancyHandler& _condRedHandler;
  const Ordering& _ordering;
  bool _fixedPointIteration;
};

ClauseIterator EqualityFactoring::generateClauses(Clause* premise)
{
  if(premise->length()<=1) {
    return ClauseIterator::getEmpty();
  }
  ASS(premise->numSelected()>0);

  auto it1 = premise->getSelectedLiteralIterator();

  auto it2 = getFilteredIterator(it1,IsPositiveEqualityFn());

  auto it3 = getMapAndFlattenIterator(it2,EqHelper::LHSIteratorFn(_salg->getOrdering()));

  auto it4 = getMapAndFlattenIterator(it3,FactorablePairsFn(premise));

  auto it5 = getMappingIterator(it4,ResultFn(*this, premise,
      getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete(),
      _salg->condRedHandler(), _salg->getOrdering(), _uwaFixedPointIteration));

  auto it6 = getFilteredIterator(it5,NonzeroFn());

  return pvi( it6 );
}

}
