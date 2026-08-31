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
 * @file TermIndex.cpp
 * Implements class TermIndex.
 */

#include "Forwards.hpp"
#include "Lib/DHSet.hpp"

#include "Inferences/InductionHelper.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "TermSubstitutionTree.hpp"
#include "CodeTreeInterfaces.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "TermIndex.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

template<bool higherOrder>
SuperpositionSubtermIndex<higherOrder>::SuperpositionSubtermIndex(SaturationAlgorithm& salg)
: TermIndex(), _ord(salg.getOrdering()) {}

template<bool higherOrder>
void SuperpositionSubtermIndex<higherOrder>::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("backward superposition index maintenance");

  for (const auto& lit : c->getSelectedLiteralIterator()) {
    for (const auto& tt : iterTraits(EqHelper::getSubtermIterator<higherOrder>(lit, _ord))) {
      _is.handle(TermLiteralClause{ tt, lit, c }, adding);
    }
  }
}

template class SuperpositionSubtermIndex<false>;
template class SuperpositionSubtermIndex<true>;

SuperpositionLHSIndex::SuperpositionLHSIndex(SaturationAlgorithm& salg)
: TermIndex(), _ord(salg.getOrdering()), _opt(salg.getOptions()) {}

void SuperpositionLHSIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("forward superposition index maintenance");

  for (const auto& lit : c->getSelectedLiteralIterator()) {
    for (const auto& lhs : iterTraits(EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt))) {
	    _is.handle(TermLiteralClause{ lhs, lit, c }, adding);
    }
  }
}

InductionTermIndex::InductionTermIndex(SaturationAlgorithm& salg)
: TermIndex(), _inductionGroundOnly(salg.getOptions().inductionGroundOnly()) {}

void InductionTermIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("induction term index maintenance");

  if (!InductionHelper::isInductionClause(c)) {
    return;
  }

  // Iterate through literals & check if the literal is suitable for induction
  for (const auto& lit : *c) {

    if (_inductionGroundOnly && !lit->ground()) {
      continue;
    }
    if (!InductionHelper::isInductionLiteral(lit)) {
      continue;
    }

    DHSet<Term*, FnvHash, PtrIdentityHash> done;
    NonVariableNonTypeIterator it(lit);
    while (it.hasNext()) {
      Term* t = it.next();
      if (!done.insert(t)) {
        it.right();
        continue;
      }
      if (InductionHelper::isInductionTerm(t) &&
          InductionHelper::isIntInductionTermListInLiteral(t, lit)) {
        if (adding) {
          _is.insert(TermLiteralClause{ t, lit, c });
        } else {
          _is.remove(TermLiteralClause{ t, lit, c });
        }
      }
    }
  }
}

StructInductionTermIndex::StructInductionTermIndex(SaturationAlgorithm& salg)
: _inductionGroundOnly(salg.getOptions().inductionGroundOnly()) {}

void StructInductionTermIndex::handleClause(Clause* c, bool adding)
{
  if (!InductionHelper::isInductionClause(c)) {
    return;
  }
  // Iterate through literals & check if the literal is suitable for induction
  for (const auto& lit : *c) {

    if (_inductionGroundOnly && !lit->ground()) {
      continue;
    }

    DHSet<Term*, FnvHash, PtrIdentityHash> done;
    NonVariableNonTypeIterator it(lit);
    while (it.hasNext()) {
      Term* t = it.next();
      if (!done.insert(t)) {
        it.right();
        continue;
      }
      if (InductionHelper::isInductionTerm(t) &&
          InductionHelper::isStructInductionTerm(t)) {
        _ct.handle(TermLiteralClause{ t, lit, c }, adding);
      }
    }
  }
}

} // namespace Indexing
