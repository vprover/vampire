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
#include "Lib/DHMap.hpp"

#include "Inferences/InductionHelper.hpp"
#include "Inferences/GoalRewriting.hpp"

#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Indexing/TermSubstitutionTree.hpp"

#include "TermIndex.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

void SuperpositionSubtermIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("backward superposition index maintenance");

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    auto rsti = EqHelper::getSubtermIterator(lit, _ord);
    while (rsti.hasNext()) {
      auto tt = TypedTermList(rsti.next());
      ((TermSubstitutionTree<TermLiteralClause>*)&*_is)->handle(TermLiteralClause{ tt, lit, c }, adding);
    }
  }
}

void SuperpositionLHSIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("forward superposition index maintenance");

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    auto lhsi = EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt);
    while (lhsi.hasNext()) {
	    _tree->handle(TermLiteralClause{ lhsi.next(), lit, c }, adding);
    }
  }
}


void DemodulationSubtermIndexImpl::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("backward demodulation index maintenance");

  static DHSet<Term*> inserted;

  if (c->goalRewritingDepth()) {
    return;
  }

  bool skipNonequationalLiterals = _opt.demodulationOnlyEquational();

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
    if (skipNonequationalLiterals && !lit->isEquality()) {
      continue;
    }

    NonVariableNonTypeIterator it(lit);
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

void DemodulationLHSIndex::handleClause(Clause* c, bool adding)
{
  if (c->length()!=1 || c->goalRewritingDepth()) {
    return;
  }

  TIME_TRACE("forward demodulation index maintenance");

  Literal* lit=(*c)[0];
  auto [lhsi, preordered] = EqHelper::getDemodulationLHSIterator(
      lit, _opt.forwardDemodulation()== Options::Demodulation::PREORDERED, _ord);

  while (lhsi.hasNext()) {
    auto lhs = lhsi.next();

    // DemodulatorData expects lhs and rhs to be normalized
    Renaming r;
    r.normalizeVariables(lhs);

    DemodulatorData dd(
      TypedTermList(r.apply(lhs),r.apply(lhs.sort())),
      r.apply(EqHelper::getOtherEqualitySide(lit, lhs)),
      c, preordered, _ord
    );
    _is->handle(std::move(dd), adding);
  }
}

void GoalRewritingLHSIndex::handleClause(Clause* c, bool adding)
{
  if (c->length()!=1 || c->goalRewritingDepth()>=_opt.maxGoalRewritingDepth()) {
    return;
  }

  Literal* lit=(*c)[0];
  if (!lit->isEquality() || lit->isNegative() || (_opt.goalRewritingChaining() && shouldChain(lit, _ord))) {
    return;
  }
  for (unsigned i = 0; i <= 1; i++) {
    auto lhs = lit->termArg(i);
    auto rhs = lit->termArg(1-i);
    if (lhs.containsAllVariablesOf(rhs)) {
      _is->handle(TermLiteralClause{ TypedTermList(lhs, SortHelper::getEqualityArgumentSort(lit)), lit, c }, adding);
    }
  }
}

void GoalRewritingSubtermIndex::handleClause(Clause* c, bool adding)
{
  if (c->length()!=1 || c->goalRewritingDepth()>=_opt.maxGoalRewritingDepth()) {
    return;
  }

  Literal* lit=(*c)[0];

  if (!lit->isEquality() || lit->isPositive() || !lit->ground()) {
    return;
  }

  DHSet<Term*> inserted;
  NonVariableNonTypeIterator it(lit);
  while (it.hasNext()) {
    Term* t = it.next();
    if (!inserted.insert(t)) {
      it.right();
      continue;
    }
    _is->handle(TermLiteralClause{ TypedTermList(t), lit, c }, adding);
  }
}

void UpwardChainingLHSIndex::handleClause(Clause* c, bool adding)
{
  if (c->length()!=1 || c->goalRewritingDepth()>=_opt.maxGoalRewritingDepth()) {
    return;
  }

  Literal* lit=(*c)[0];
  if (!lit->isEquality() || lit->isNegative()) {
    return;
  }
  if (_left == shouldChain(lit, _ord)) {
    return;
  }
  if (_left) {
    auto lhsi = EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt);
    while (lhsi.hasNext()) {
      auto lhs = EqHelper::getOtherEqualitySide(lit,lhsi.next());
	    _is->handle(TermLiteralClause{ TypedTermList(lhs, SortHelper::getEqualityArgumentSort(lit)), lit, c }, adding);
    }
  } else {
    switch (_ord.getEqualityArgumentOrder(lit)) {
      case Ordering::LESS: {
        _is->handle(TermLiteralClause{ TypedTermList(lit->termArg(1), SortHelper::getEqualityArgumentSort(lit)), lit, c }, adding);
        break;
      }
      case Ordering::GREATER: {
        _is->handle(TermLiteralClause{ TypedTermList(lit->termArg(0), SortHelper::getEqualityArgumentSort(lit)), lit, c }, adding);
        break;
      }
      default:
        ASSERTION_VIOLATION;
    }
  }
}

void UpwardChainingSubtermIndex::handleClause(Clause* c, bool adding)
{
  if (c->length()!=1 || c->goalRewritingDepth()>=_opt.maxGoalRewritingDepth()) {
    return;
  }

  Literal* lit=(*c)[0];

  if (!lit->isEquality() || lit->isNegative()) {
    return;
  }

  if (_left != shouldChain(lit, _ord)) {
    return;
  }
  DHSet<Term*> inserted;
  if (_left) {
    auto comp = _ord.getEqualityArgumentOrder(lit);
    ASS(comp != Ordering::INCOMPARABLE && comp != Ordering::EQUAL);
    auto t = lit->termArg(comp == Ordering::LESS ? 0 : 1);
    if (t.isVar()) {
      return;
    }
    NonVariableNonTypeIterator nvi(t.term(),true);
    while (nvi.hasNext()) {
      Term* st = nvi.next();
      if (!inserted.insert(st)) {
        nvi.right();
        continue;
      }
      _is->handle(TermLiteralClause{ st, lit, c }, adding);
    }
  } else {
    auto lhsi = EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt);
    while (lhsi.hasNext()) {
      auto lhs = EqHelper::getOtherEqualitySide(lit,lhsi.next());
      if (lhs.isVar()) {
        continue;
      }
      NonVariableNonTypeIterator nvi(lhs.term(),true);
      while (nvi.hasNext()) {
        auto st = nvi.next();
        if (!inserted.insert(st)) {
          nvi.right();
          continue;
        }
        _is->handle(TermLiteralClause{ st, lit, c }, adding);
      }
    }
  }
}

void InductionTermIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("induction term index maintenance");

  if (!InductionHelper::isInductionClause(c)) {
    return;
  }

  // Iterate through literals & check if the literal is suitable for induction
  for (unsigned i=0;i<c->length();i++) {
    Literal* lit = (*c)[i];
    if (!InductionHelper::isGroundInductionLiteral(lit)) {
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
      if (t->isLiteral()) {
        continue;
      }
      if (InductionHelper::isInductionTermFunctor(t->functor()) &&
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

void StructInductionTermIndex::handleClause(Clause* c, bool adding)
{
  if (!InductionHelper::isInductionClause(c)) {
    return;
  }
  static DHSet<Term*> inserted;
  // Iterate through literals & check if the literal is suitable for induction
  for (unsigned i=0;i<c->length();i++) {
    inserted.reset();
    Literal* lit = (*c)[i];
    if (!lit->ground()) {
      continue;
    }
    NonVariableNonTypeIterator it(lit);
    while (it.hasNext()) {
      Term* t = it.next();
      if (!inserted.insert(t)) {
        it.right();
        continue;
      }
      if (t->isLiteral()) {
        continue;
      }
      if (InductionHelper::isInductionTermFunctor(t->functor()) &&
          InductionHelper::isStructInductionTerm(t)) {
        if (adding) {
          _is->insert(TermLiteralClause{ t, lit, c });
        } else {
          _is->remove(TermLiteralClause{ t, lit, c });
        }
      }
    }
  }
}

void SkolemisingFormulaIndex::insertFormula(TermList formula, TermList skolem)
{
  _is->insert(TermWithValue<TermList>(TypedTermList(formula.term()), skolem));
}

} // namespace Indexing
