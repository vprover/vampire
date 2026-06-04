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

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/LiteralSelector.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "EqualityResolution.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

constexpr unsigned kVarBank = 0;

namespace {

Clause* unifierToClause(Clause* cl, Literal* lit, AbstractingUnifier* unif, const Ordering* ord, HOLUnificationHandler* holHandler)
{
  RStack<Literal*> resLits;
  Literal* litAfter = 0;

  if (ord && cl->numSelected() > 1) {
    TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
    litAfter = unif->subs().apply(lit, kVarBank);
  }

  for (unsigned i = 0; i < cl->length(); i++) {
    auto curr=(*cl)[i];
    if (curr == lit) {
      continue;
    }
    auto currAfter = unif->subs().apply(curr, kVarBank);

    if (litAfter) {
      TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

      if (i < cl->numSelected() && ord->compare(currAfter,litAfter) == Ordering::GREATER) {
        env.statistics->inferencesBlockedDueToOrderingAftercheck++;
        return nullptr;
      }
    }

    resLits->push(currAfter);
  }

  auto [constraints, defs] = unif->computeConstraintLiterals(holHandler);
  resLits->loadFromIterator(constraints->iterFifo());

  auto prems = UnitList::fromIterator(defs->iter());
  UnitList::push(cl, prems);
  auto res = Clause::fromStack(*resLits, GeneratingInferenceMany(InferenceRule::EQUALITY_RESOLUTION, prems));
  if(env.options->proofExtra() == Options::ProofExtra::FULL)
    env.proofExtra.insert(res, new EqualityResolutionExtra(lit));
  return res;
}

}

ClauseIterator EqualityResolution::generateClauses(Clause* premise)
{
  static AbstractingUnifier unif;

  return pvi(premise->getSelectedLiteralIterator()
    .filter([](Literal* l)  { return l->isEquality() && l->isNegative(); })
    .flatMap([this,premise](Literal* lit) {

      AbstractionOracle abstractionOracle(_salg.getOptions().unificationWithAbstraction());

      auto [lhs, rhs] = lit->eqArgs();

      // We only care about non-trivial constraints where the top-sybmol of the two literals are the same
      // and therefore a constraint can be created between arguments
      if(lhs.isTerm() && rhs.isTerm() &&
        lhs.term()->functor() != rhs.term()->functor() && _salg.getOptions().unificationWithAbstraction() != Shell::Options::UnificationWithAbstraction::HOL){
        abstractionOracle = AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF);
      }

      unif.init(abstractionOracle);
      if (!unif.unify(lhs, kVarBank, rhs, kVarBank, _salg.getOptions().unificationWithAbstractionFixedPointIteration())) {
        return ClauseIterator::getEmpty();
      }

      return pvi(iterTraits(vi(new HOL::AbstractingWrapper(&unif, _salg.getOptions().higherOrderUnifDepth())))
        .map([this,premise,lit](AbstractingUnifier* unif) {
          return unifierToClause(premise, lit, unif, _salg.getOptions().literalMaximalityAftercheck() && _salg.getLiteralSelector().isBGComplete() ? &_salg.getOrdering() : nullptr, _salg.holUnificationHandler());
        }));
      })
    .filter(NonzeroFn()));
}

}
