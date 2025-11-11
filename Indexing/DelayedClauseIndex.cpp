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
 * @file DelayedClauseIndex.cpp
 * Implements class DelayedClauseIndex.
 */

#include "DelayedClauseIndex.hpp"

#include "TermIndex.hpp"
#include "LiteralIndex.hpp"

#include "Kernel/EqHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Indexing {

void DelayedClauseIndex::attach(SaturationAlgorithm* salg)
{
  _ord = &salg->getOrdering();
  _opt = &salg->getOptions();

  auto imgr = salg->getIndexManager();
  _goalSubtermIndex = static_cast<SuperpositionSubtermIndex<true>*>(imgr->request(GOAL_SUBTERM_INDEX));
  _goalLHSIndex = static_cast<SuperpositionLHSIndex<true>*>(imgr->request(GOAL_LHS_INDEX));
  _goalLiteralIndex = static_cast<BinaryResolutionIndex<true>*>(imgr->request(GOAL_LITERAL_INDEX));
  _goalPredicateIndex = static_cast<GoalDirectedPredicateIndex*>(imgr->request(GOAL_PREDICATE_INDEX));
}
// TODO detach

bool DelayedClauseIndex::checkReachableOrInsert(Clause* cl)
{
  for (unsigned i = 0; i < cl->length(); i++) {
    auto lit = (*cl)[i];
    if (!checkReachable(lit)) {
      handle(cl, lit, /*adding=*/true);
      ALWAYS(_clauses.insert(cl, i));
      return false;
    }
  }
  return true;
}

void DelayedClauseIndex::remove(Clause* cl)
{
  unsigned index = 0;
  ALWAYS(_clauses.pop(cl, index));
  handle(cl, (*cl)[index], /*adding=*/false);
}

bool DelayedClauseIndex::checkReachable(Literal* lit)
{
  if (lit->isNegative()) {
    return true;
  }
  if (!lit->isEquality()) {
    if (_predIS.findPtr(lit->functor())) {
      if (_goalLiteralIndex->getUnifications(lit, /*complementary=*/true, /*retrieveSubstitutions=*/false).hasNext()) {
        return true;
      }
      for (const auto& st : iterTraits(NonVariableNonTypeIterator(lit))) {
        if (_goalLHSIndex->getUnifications(st, false).hasNext()) {
          return true;
        }
      }
    }
    return false;
  }

  auto linearizedTypedTerm = [](TermList t, TermList sort) {
    if (t.isVar()) {
      return TypedTermList(t, sort);
    }
    return TypedTermList(Term::linearize(t.term()));
  };

  auto eqSort = SortHelper::getEqualityArgumentSort(lit);

  auto lhs = linearizedTypedTerm(lit->termArg(0), eqSort);
  if (_goalSubtermIndex->getUnifications(lhs, false).hasNext()) {
    return true;
  }

  auto rhs = linearizedTypedTerm(lit->termArg(1), eqSort);
  if (_goalSubtermIndex->getUnifications(rhs, false).hasNext()) {
    return true;
  }

  auto checkSubterms = [this](TypedTermList t) {
    return t.isTerm() &&
      iterTraits(NonVariableNonTypeIterator(t.term(), true))
        .any([this](auto st) { return _goalLHSIndex->getUnifications(st, false).hasNext(); });
  };

  switch (_ord->compare(lit->termArg(0), lit->termArg(1))) {
    case Ordering::GREATER:
      return checkSubterms(lhs);
    case Ordering::LESS:
      return checkSubterms(rhs);
    case Ordering::INCOMPARABLE:
      return checkSubterms(lhs) || checkSubterms(rhs);
    default:
      break;
  }
  ASSERTION_VIOLATION;
}

void DelayedClauseIndex::handle(Clause* cl, Literal* lit, bool adding)
{
  ASS(lit->isPositive()); // we only have to index positive literals

  // SubtermIndex
  for (TypedTermList tt : iterTraits(EqHelper::getSubtermIterator(lit, *_ord))) {
    // TODO don't linearize here
    if (tt.isTerm()) {
      tt = Term::linearize(tt.term());
    }
    _subtermIS.handle(TermLiteralClause{ tt, lit, cl }, adding);
  }

  if (lit->isEquality()) {
    // PositiveEqualitySideIndex
    for (unsigned i = 0; i < 2; i++) {
      TypedTermList tt(lit->termArg(i), SortHelper::getEqualityArgumentSort(lit));
      if (tt.isTerm()) {
        tt = Term::linearize(tt.term());
      }
      _posEqSideIS.handle(TermLiteralClause{ tt, lit, cl }, adding);
    }
  } else {
    // PositiveLiteralIndex
    _posLitIS.handle(LiteralLiteralClause{ Literal::linearize(lit), lit, cl }, adding);

    // PredicateIndex
    DHMap<Clause*,Literal*>* ptr;
    _predIS.getValuePtr(lit->functor(), ptr);
    if (adding) {
      ALWAYS(ptr->insert(cl, lit));
    } else {
      ASS(ptr);
      ptr->remove(cl);
    }
  }
}

ClauseStack DelayedClauseIndex::maybeUndelayClauses(Clause* cl)
{
  DHMap<Clause*,Literal*> toPassive;

  for (const auto& lit : cl->getSelectedLiteralIterator()) {
    if (!lit->isEquality()) {
      if (lit->isNegative()) {
        // direct unification
        auto litl = Literal::linearize(lit);
        for (const auto& qr : iterTraits(_posLitIS.getUnifications(litl, /*complementary=*/true, /*retrieveSubstitutions=*/false))) {
          toPassive.insert(qr.data->clause, qr.data->origLiteral);
        }
        // otherwise we check whether the predicate functor is present in a complementary
        // literal and check all its subterms for superposition candidates
        auto predMap = _predIS.findPtr(litl->functor());
        if (predMap) {
          for (const auto& [qcl,qlit] : iterTraits(predMap->items())) {
            for (const auto& st : iterTraits(NonVariableNonTypeIterator(qlit))) {
              if (_goalLHSIndex->getUnifications(st, /*retrieveSubstitutions=*/false).hasNext()) {
                toPassive.insert(qcl, qlit);
                break;
              }
            }
          }
        }
      }
    } else {
      for (auto lhs : iterTraits(EqHelper::getSuperpositionLHSIterator(lit, *_ord, *_opt))) {
        if (lhs.isTerm()) {
          lhs = Term::linearize(lhs.term());
        }
        for (const auto& qr : iterTraits(_subtermIS.getUnifications(lhs, /*retrieveSubstitutions=*/false))) {
          toPassive.insert(qr.data->clause, qr.data->literal);
        }
      }
    }

    for (auto st : iterTraits(EqHelper::getSubtermIterator(lit, *_ord))) {
      st = Term::linearize(st);
      for (const auto& qr : iterTraits(_posEqSideIS.getUnifications(st, /*retrieveSubstitutions=*/false))) {
        toPassive.insert(qr.data->clause, qr.data->literal);
      }
    }
  }

  ClauseStack res;

  for (const auto& [qcl, qlit] : iterTraits(toPassive.items())) {
    ASS(checkReachable(qlit));
    // remove this lit from the index
    handle(qcl, qlit, /*adding=*/false);
    unsigned* index = _clauses.findPtr(qcl);
    ASS(index);
    ASS_EQ(*index, qcl->getLiteralPosition(qlit));

    // insert next
    bool undelay = true;
    for (; *index < qcl->length(); (*index)++) {
      if (!checkReachable((*qcl)[*index])) {
        handle(qcl, (*qcl)[*index], /*adding=*/true);
        undelay = false;
        break;
      }
    }
    if (undelay) {
      ALWAYS(_clauses.remove(qcl));
      res.push(qcl);
    }
  }
  return res;
}

} // namespace Indexing
