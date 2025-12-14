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
 * @file GoalReachabilityHandler.cpp
 * Implements class GoalReachabilityHandler.
 */

#include "GoalReachabilityHandler.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Lib/Exception.hpp"

using namespace Shell;
using namespace Kernel;

#define DEBUG(...) // DBG(__VA_ARGS__)

constexpr unsigned kIterationLimit = 10;

// This is different from EqHelper::getSuperpositionLHSIterator because it works for negative equalities too
VirtualIterator<TypedTermList> getLHSIterator(Literal* lit, const Ordering& ord)
{
  ASS(lit->isEquality());
  auto sort = SortHelper::getEqualityArgumentSort(lit);
  auto lhs = lit->termArg(0);
  auto rhs = lit->termArg(1);
  switch (ord.getEqualityArgumentOrder(lit)) {
    case Ordering::INCOMPARABLE:
      return pvi(iterItems(TypedTermList(lhs, sort), TypedTermList(rhs, sort)));
    case Ordering::GREATER:
      return pvi(iterItems(TypedTermList(lhs, sort)));
    case Ordering::LESS:
      return pvi(iterItems(TypedTermList(rhs, sort)));
    //there should be no equality literals of equal terms
    case Ordering::EQUAL:
      ASSERTION_VIOLATION;
  }
}

bool GoalReachabilityHandler::addClause(Clause* cl)
{
  if (cl->length() != 1) {
    INVALID_OPERATION("only unit clauses are supported");
  }

  auto lit = (*cl)[0];
  if (!lit->isEquality()) {
    INVALID_OPERATION("only equality is supported");
  }

  // We check whether the clause is a goal clause or not.

  // It is a goal clause if the literal is negative
  if (lit->isNegative()) {
    goto GOAL_CLAUSE;
  }

  {
    auto tree = new ReachabilityTree(*this);
    for (const auto& lhs : iterTraits(getLHSIterator(lit, ord))) {
      if (!tree->addTerm(TypedTermList(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort()))) {
        goto GOAL_CLAUSE;
      }
    }
    ALWAYS(clauseTrees.insert(cl, tree));
    return false;
  }

  // If it is, it possibly contributes to some reachibility
  // trees, so we insert it as such
GOAL_CLAUSE:
  addGoalClause(cl);
  return true;
}

void GoalReachabilityHandler::addGoalClause(Clause* cl)
{
  DEBUG("goal clause added ", *cl);
  ASS_EQ(cl->length(),1);

  auto lit = (*cl)[0];
  ASS(lit->isEquality());

  // 1. Insert all strict subterms of the greater side into indices.
  // Note: this has to be done before step 2 below
  for (auto lhs : iterTraits(getLHSIterator(lit, ord))) {
    if (lhs.isVar()) { continue; }
    for (const auto& st : iterTraits(NonVariableNonTypeIterator(lhs.term(), /*includeSelf=*/lit->isNegative()))) {
      DEBUG("adding to goal lhs index ", *st);
      _goalSubtermIndex.insert({ st, lhs, lit, cl });
    }
  }

  // 2. Iterate reachibility trees
  for (auto lhs : iterTraits(getLHSIterator(lit, ord))) {
    if (lhs.isVar()) { continue; }
    TypedTermList rhs(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort());
    for (const auto& st : iterTraits(NonVariableNonTypeIterator(lhs.term(), /*includeSelf=*/lit->isNegative()))) {
      for (const auto& qr : iterTraits(_rhsIndex.getUnifications(st, /*retrieveSubstitutions=*/true))) {

        if (lit->isNegative()) {
          // TODO handle case when qr.data->clause becomes goal clause
          INVALID_OPERATION("clause becomes goal is not handled");
        } else {
          auto& tree = clauseTrees.get(qr.data->clause);
          if (!tree->canBeAdded(rhs, *qr.unifier.ptr(), /*result=*/false)) {
            // TODO handle case when qr.data->clause becomes goal clause
            INVALID_OPERATION("clause becomes goal is not handled");
          }
          tree->addTerm(qr.unifier->apply(rhs, /*result=*/false));
        }
      }
    }
  }
}

bool GoalReachabilityHandler::ReachabilityTree::addTerm(TypedTermList t)
{
  DEBUG("adding term ", t.untyped());

  Stack<TypedTermList> todo;
  todo.push(t);

  unsigned iterCnt = 0;

  while (todo.isNonEmpty()) {
    auto curr = todo.pop();
    DEBUG("iterating ", curr.untyped());

    if (++iterCnt == kIterationLimit) {
      // we reached the limit, giving up
      return false;
    }

    // we have already inserted this term
    if (!terms.insert(curr)) {
      DEBUG("already contains ", curr.untyped());
      return true;
    }

    for (const auto& qr : iterTraits(handler._goalSubtermIndex.getUnifications(curr, /*retrieveSubstitutions=*/true))) {
      DEBUG("unified with term ", qr.data->term.untyped(), " (", qr.unifier->apply(qr.data->term, /*result=*/true).untyped(),
        ") in literal ", *qr.data->literal, " (", *qr.unifier->apply(qr.data->literal, /*result=*/true), ")");
      auto lhs = qr.data->side;
      if (qr.data->literal->isNegative()) {
        // we reached a goal directly
        return false;
      }
      TypedTermList rhs(EqHelper::getOtherEqualitySide(qr.data->literal, lhs), lhs.sort());

      // if a term cannot be added, then we can reach the goal
      if (!canBeAdded(rhs, *qr.unifier.ptr(), /*result=*/true)) {
        return false;
      }
      todo.push(qr.unifier->apply(rhs, /*result=*/true));
    }
  }
  return true;
}

bool GoalReachabilityHandler::ReachabilityTree::canBeAdded(TypedTermList t, ResultSubstitution& subst, bool result)
{
  DEBUG("can be added? ", t.untyped(), " ", subst.apply(t, result).untyped());

  DHSet<TermList> renamingDomain;
  DHSet<TermList> renamingRange;

  VariableIterator it(t);
  while(it.hasNext()) {
    TermList v = it.next();
    ASS(v.isVar());
    if (!renamingDomain.insert(v)) {
      continue;
    }

    TermList vSubst = subst.apply(v, result);
    if (!vSubst.isVar() || !renamingRange.insert(vSubst)) {
      // not renaming, term can be inserted
      return true;
    }
  }
  // renaming, term should not be inserted
  return false;
}

