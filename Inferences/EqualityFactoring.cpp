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
#include "Kernel/HOL/Unifier.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/LiteralSelector.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "EqualityFactoring.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using std::pair;

constexpr unsigned kVarBank = 0;

namespace {

Clause* unifierToClause(Clause* cl, TermList srt, Literal* sLit, TermList sLHS, Literal* fLit, TermList fLHS, AbstractingUnifier* absUnif, const Ordering& ord, const bool afterCheck)
{
  TermList srtS = absUnif->subs().apply(srt,kVarBank);
  TermList sLHSS = absUnif->subs().apply(sLHS,kVarBank);
  TermList sRHSS = absUnif->subs().apply(EqHelper::getOtherEqualitySide(sLit, sLHS),kVarBank);
  if(Ordering::isGreaterOrEqual(ord.compare(sRHSS,sLHSS))) {
    return nullptr;
  }
  auto fRHS = EqHelper::getOtherEqualitySide(fLit, fLHS);
  TermList fRHSS = absUnif->subs().apply(fRHS,kVarBank);
  if(Ordering::isGreaterOrEqual(ord.compare(fRHSS,sLHSS))) {
    return nullptr;
  }
  auto constraints = absUnif->computeConstraintLiterals();

  RStack<Literal*> resLits;
  resLits->push(Literal::createEquality(false, sRHSS, fRHSS, srtS));

  Literal* sLitAfter = 0;
  if (afterCheck && cl->numSelected() > 1) {
    TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
    sLitAfter = absUnif->subs().apply(sLit, kVarBank);
  }

  for (unsigned i = 0; i < cl->length(); i++) {
    Literal* curr = (*cl)[i];
    if (curr == sLit) {
      continue;
    }
    Literal* currAfter = absUnif->subs().apply(curr, kVarBank);

    if (sLitAfter) {
      TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
      if (i < cl->numSelected() && ord.compare(currAfter,sLitAfter) == Ordering::GREATER) {
        env.statistics->inferencesBlockedDueToOrderingAftercheck++;
        return nullptr;
      }
    }

    resLits->push(currAfter);
  }

  resLits->loadFromIterator(constraints->iterFifo());

  auto res = Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::EQUALITY_FACTORING, cl));
  if(env.options->proofExtra() == Options::ProofExtra::FULL)
    env.proofExtra.insert(res, new EqualityFactoringExtra(sLit, fLit, sLHS, fRHS));
  return res;
}

}

EqualityFactoring::EqualityFactoring(SaturationAlgorithm& salg)
  : _salg(salg)
  , _abstractionOracle(_salg.getOptions().unificationWithAbstraction())
  , _uwaFixedPointIteration(_salg.getOptions().unificationWithAbstractionFixedPointIteration())
{}

ClauseIterator EqualityFactoring::generateClauses(Clause* premise)
{
  static AbstractingUnifier unif;
  static bool funcExt = _salg.getOptions().functionExtensionality()==Options::FunctionExtensionality::ABSTRACTION;

  return pvi(premise->getSelectedLiteralIterator()
    .filter([](Literal* l){
      return l->isEquality() && l->isPositive();
    })
    .flatMap([this](Literal* lit) {
      return pvi( pushPairIntoRightIterator(lit, EqHelper::getLHSIterator(lit, _salg.getOrdering())) );
    })
    .flatMap([premise](pair<Literal*,TermList> arg) {
      return pvi(pushPairIntoRightIterator(arg, premise->iterLits()
        .filter([arg](Literal* l2){
          return l2->isEquality() && l2->isPositive() && l2 != arg.first;
        })
        .flatMap([](Literal* l2) {
          auto [lhs,rhs] = l2->eqArgs();
          return pvi( pushPairIntoRightIterator(l2, iterItems( lhs, rhs ) ) );
        })));
    })
    .flatMap([=,this](pair<pair<Literal*,TermList>,pair<Literal*,TermList> > arg) {
      auto [p1, p2] = arg;
      auto [sLit, sLHS] = p1; // selected literal ( = factored-out literal ) and side of equation
      auto [fLit, fLHS] = p2; // fairly boring side literal and side of equation
      ASS_NEQ(sLit, fLit);

      TermList srt = SortHelper::getEqualityArgumentSort(sLit);

      unif.init(_abstractionOracle);
      if (!unif.unifyOnce(srt, kVarBank, SortHelper::getEqualityArgumentSort(fLit), kVarBank)) {
        return ClauseIterator::getEmpty();
      }

      if (!unif.unify(sLHS, kVarBank, fLHS, kVarBank, _uwaFixedPointIteration)) {
        return ClauseIterator::getEmpty();
      }

      return pvi(iterTraits(HOL::AbstractingWrapper::create(unif, _salg.getOptions().higherOrderUnifDepth(), funcExt))
        .map([=,this](AbstractingUnifier* unif) {
          return unifierToClause(premise, srt, sLit, sLHS, fLit, fLHS, unif, _salg.getOrdering(), _salg.getOptions().literalMaximalityAftercheck() && _salg.getLiteralSelector().isBGComplete());
        }));
    })
    .filter(NonzeroFn()));
}

}
