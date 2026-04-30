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

SuperpositionSubtermIndex::SuperpositionSubtermIndex(SaturationAlgorithm& salg)
: TermIndex(new TermSubstitutionTree<TermLiteralClause>), _ord(salg.getOrdering()), _higherOrder(env.higherOrder()) {}

void SuperpositionSubtermIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("backward superposition index maintenance");

  for (const auto& lit : c->getSelectedLiteralIterator()) {
    for (const auto& tt : iterTraits(EqHelper::getSubtermIterator(lit, _ord, _higherOrder))) {
      _is->handle(TermLiteralClause{ tt, lit, c }, adding);
    }
  }
}

SuperpositionLHSIndex::SuperpositionLHSIndex(SaturationAlgorithm& salg)
: TermIndex(new TermSubstitutionTree<TermLiteralClause>), _ord(salg.getOrdering()), _opt(salg.getOptions()) {}

void SuperpositionLHSIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("forward superposition index maintenance");

  for (const auto& lit : c->getSelectedLiteralIterator()) {
    for (const auto& lhs : iterTraits(EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt))) {
	    _is->handle(TermLiteralClause{ lhs, lit, c }, adding);
    }
  }
}

template<bool higherOrder>
DemodulationSubtermIndex<higherOrder>::DemodulationSubtermIndex(SaturationAlgorithm& salg)
: TermIndex(new TermSubstitutionTree<TermLiteralClause>()),
  _skipNonequationalLiterals(salg.getOptions().demodulationOnlyEquational()) {};

template<bool higherOrder>
void DemodulationSubtermIndex<higherOrder>::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("backward demodulation index maintenance");

  static DHSet<Term*> inserted;

  unsigned cLen=c->length();
  for (unsigned i=0; i<cLen; i++) {
    // it is true (as stated below) that inserting only once per clause would be sufficient
    // however, vampire does not guarantee the order of literals stays the same in a clause (selected literals are moved to front)
    // so if the order changes while a clause is in the index (which can happen with "-sa otter")
    // the removes could be called on different literals than the inserts!
    inserted.reset();
    Literal* lit=(*c)[i];
    if (lit->isAnswerLiteral()) {
      continue;
    }
    if (_skipNonequationalLiterals && !lit->isEquality()) {
      continue;
    }

    RewritableSubtermIterator<higherOrder> it(lit);
    while (it.hasNext()) {
      Term* t= it.next();
      if (!inserted.insert(t)) {//TODO existing error? Terms are inserted once per a literal
        //It is enough to insert a term only once per clause.
        //Also, once we know term was inserted, we know that all its
        //subterms were inserted as well, so we can skip them.
        it.right();
        continue;
      }
      if (adding) {
        _is->insert(TermLiteralClause{ t, lit, c });
      } else {
        _is->remove(TermLiteralClause{ t, lit, c });
      }
    }
  }
}

template class DemodulationSubtermIndex<true>;
template class DemodulationSubtermIndex<false>;

template<bool higherOrder>
DemodulationLHSIndex<higherOrder>::DemodulationLHSIndex(SaturationAlgorithm& salg)
: _ord(salg.getOrdering()), _preordered(salg.getOptions().forwardDemodulation()==Options::Demodulation::PREORDERED) {}

template<bool higherOrder>
void DemodulationLHSIndex<higherOrder>::handleClause(Clause* c, bool adding)
{
  if (c->length()!=1) {
    return;
  }

  TIME_TRACE("forward demodulation index maintenance");

  Literal* lit=(*c)[0];
  auto [lhsi, preordered] = EqHelper::getDemodulationLHSIterator(lit, _preordered, _ord);

  for (const auto& lhs : iterTraits(std::move(lhsi))) {
    // DemodulatorData expects lhs and rhs to be normalized
    Renaming r;
    r.normalizeVariables(lhs);
    auto sortR = r.apply(lhs.sort());

    DemodulatorData dd(
      TypedTermList(r.apply(lhs),sortR),
      TypedTermList(r.apply(EqHelper::getOtherEqualitySide(lit, lhs)),sortR),
      c, preordered, _ord
    );
    GeneralizingTermIndex<higherOrder, DemodulatorData>::_ct.handle(std::move(dd), adding);
  }
}

template class DemodulationLHSIndex<true>;
template class DemodulationLHSIndex<false>;

InductionTermIndex::InductionTermIndex(SaturationAlgorithm& salg)
: TermIndex(new TermSubstitutionTree<TermLiteralClause>()), _inductionGroundOnly(salg.getOptions().inductionGroundOnly()) {}

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

    DHSet<Term*> done;
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
          _is->insert(TermLiteralClause{ t, lit, c });
        } else {
          _is->remove(TermLiteralClause{ t, lit, c });
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

    DHSet<Term*> done;
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

SkolemisingFormulaIndex::SkolemisingFormulaIndex(SaturationAlgorithm&) {}

void SkolemisingFormulaIndex::insertFormula(TermList formula, TermList skolem)
{
  _ct.handle(TermWithValue<TermList>(TypedTermList(formula.term()), skolem), /*insert=*/true);
}

} // namespace Indexing
