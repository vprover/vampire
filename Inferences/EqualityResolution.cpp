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

#include "Kernel/UnificationWithAbstraction.hpp"
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

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/ConditionalRedundancyHandler.hpp"

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
  { return l->isEquality() && l->isNegative(); }
};

struct EqualityResolution::ResultFn
{
  ResultFn(Clause* cl, bool afterCheck = false, const ConditionalRedundancyHandler* condRedHandler = nullptr, Ordering* ord = nullptr)
      : _afterCheck(afterCheck), _condRedHandler(condRedHandler), _ord(ord), _cl(cl), _cLen(cl->length()) {}

  Clause* operator() (std::pair<Literal*, AbstractingUnifier> pair)
  {
    auto lit = pair.first;
    auto* absUnif = &pair.second;

    ASS(lit->isEquality());
    ASS(lit->isNegative());

    auto constraints = absUnif->computeConstraintLiterals();

    RStack<Literal*> resLits;

    Literal* litAfter = 0;

    if (_afterCheck && _cl->numSelected() > 1) {
      TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
      litAfter = absUnif->subs().apply(lit, 0);
    }

    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=lit) {
        Literal* currAfter = absUnif->subs().apply(curr, 0);

        if (litAfter) {
          TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

          if (i < _cl->numSelected() && _ord->compare(currAfter,litAfter) == Ordering::GREATER) {
            env.statistics->inferencesBlockedForOrderingAftercheck++;
            return nullptr;
          }
        }

        resLits->push(currAfter);
      }
    }

    if (!absUnif->usesUwa()) {
      if (_condRedHandler && !_condRedHandler->handleReductiveUnaryInference(_cl, &absUnif->subs())) {
        env.statistics->skippedEqualityResolution++;
        return nullptr;
      }
    }

    resLits->loadFromIterator(constraints->iterFifo());

    env.statistics->equalityResolution++;

    Clause *cl = Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::EQUALITY_RESOLUTION, _cl));
    if(env.options->proofExtra() == Options::ProofExtra::FULL)
      env.proofExtra.insert(cl, new EqualityResolutionExtra(lit));
    return cl;
  }
private:
  bool _afterCheck;
  const ConditionalRedundancyHandler* _condRedHandler;
  const Ordering* _ord;
  Clause* _cl;
  unsigned _cLen;
};

struct EqualityResolution::PotentialApplicationIters {
  EqualityResolution& self;
  auto iterAppls(Clause* cause, Literal* lit) {
  return iterItems(lit)
    .filter(IsNegativeEqualityFn())
    .filterMap([](auto lit) -> Option<std::pair<Literal*, AbstractingUnifier>> {

      static AbstractionOracle _abstractionOracle = AbstractionOracle::create();
      auto abstractionOracle = _abstractionOracle;

      TermList arg0 = lit->termArg(0);
      TermList arg1 = lit->termArg(1);

      // We only care about non-trivial constraints where the top-sybmol of the two literals are the same
      // and therefore a constraint can be created between arguments
      if(arg0.isTerm() && arg1.isTerm() &&
         arg0.term()->functor() != arg1.term()->functor()){
        abstractionOracle = AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF);
      }

      if (auto unif =  AbstractingUnifier::unify(arg0, 0, arg1, 0, abstractionOracle, env.options->unificationWithAbstractionFixedPointIteration())) {
        return some(std::make_pair(lit, std::move(*unif)));
      } else {
        return {};
      }
    });
  }
};


VirtualIterator<std::tuple<>> EqualityResolution::lookaheadResultEstimation(__SelectedLiteral const& selection) 
{ return pvi(dropElementType(PotentialApplicationIters{*this}.iterAppls(selection.clause(), selection.literal()))); }

ClauseIterator EqualityResolution::generateClauses(Clause* premise)
{
  if(premise->isEmpty()) {
    return ClauseIterator::getEmpty();
  }
  ASS(premise->numSelected()>0);

  return pvi(
      premise->getSelectedLiteralIterator()
      .flatMap([=](auto l) { return PotentialApplicationIters{*this}.iterAppls(premise, l); })
      .map(ResultFn(premise,
                    getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete(),
                    &_salg->condRedHandler(), 
                    &_salg->getOrdering()))
      .filter(NonzeroFn()));
}

}
