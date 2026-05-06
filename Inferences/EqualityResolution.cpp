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

struct EqualityResolution::IsNegativeEqualityFn
{
  bool operator()(Literal* l)
  { return l->isEquality() && l->isNegative(); }
};

struct EqualityResolution::ResultFn
{
  ResultFn(Clause* cl, bool afterCheck = false, const Ordering* ord = nullptr, HOLUnificationHandler* holHandler = nullptr)
      : _afterCheck(afterCheck), _ord(ord), _cl(cl), _cLen(cl->length()), _holHandler(holHandler) {}

  Clause* operator() (Literal* lit)
  {
    ASS(lit->isEquality());
    ASS(lit->isNegative());

    static AbstractionOracle _abstractionOracle = AbstractionOracle::create();
    auto abstractionOracle = _abstractionOracle;

    auto [lhs, rhs] = lit->eqArgs();

    // We only care about non-trivial constraints where the top-sybmol of the two literals are the same
    // and therefore a constraint can be created between arguments
    if(lhs.isTerm() && rhs.isTerm() &&
       lhs.term()->functor() != rhs.term()->functor() && env.options->unificationWithAbstraction() != Shell::Options::UnificationWithAbstraction::HOL){
      abstractionOracle = AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF);
    }

    auto absUnif = AbstractingUnifier::unify(lhs, 0, rhs, 0, abstractionOracle, env.options->unificationWithAbstractionFixedPointIteration(), _holHandler);

    if(absUnif.isNone()){ 
      return 0; 
    }

    auto [constraints, defs] = absUnif->computeConstraintLiterals();

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
            env.statistics->inferencesBlockedDueToOrderingAftercheck++;
            return nullptr;
          }
        }

        resLits->push(currAfter);
      }
    }

    resLits->loadFromIterator(constraints->iterFifo());

    auto prems = UnitList::fromIterator(defs->iter());
    UnitList::push(_cl, prems);
    Clause *cl = Clause::fromStack(*resLits, GeneratingInferenceMany(InferenceRule::EQUALITY_RESOLUTION, prems));
    if(env.options->proofExtra() == Options::ProofExtra::FULL)
      env.proofExtra.insert(cl, new EqualityResolutionExtra(lit));
    return cl;
  }
private:
  bool _afterCheck;
  const Ordering* _ord;
  Clause* _cl;
  unsigned _cLen;
  HOLUnificationHandler* _holHandler;
};

ClauseIterator EqualityResolution::generateClauses(Clause* premise)
{
  return pvi(premise->getSelectedLiteralIterator()
    .filter(IsNegativeEqualityFn())
    .map(ResultFn(premise,
      _salg.getOptions().literalMaximalityAftercheck() && _salg.getLiteralSelector().isBGComplete(),
      &_salg.getOrdering(), _salg.holUnificationHandler()))
    .filter(NonzeroFn()));
}

/**
 * @c toResolve must be an negative equality. If it is resolvable,
 * resolve it and return the resulting clause. If it is not resolvable,
 * return 0.
 */
Clause* EqualityResolution::tryResolveEquality(Clause* cl, Literal* toResolve)
{
  return ResultFn(cl)(toResolve);
}

}
