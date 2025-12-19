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
#include "Kernel/TermTransformer.hpp"
#include "Kernel/TypedTermList.hpp"

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

std::pair<ClauseStack, ClauseTermPairs> GoalReachabilityHandler::addClause(Clause* cl)
{
  DEBUG("addClause ", *cl);
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
    auto tree = new ReachabilityTree(*this, cl);
    for (const auto& lhs : iterTraits(getLHSIterator(lit, ord))) {
      if (!tree->addTerm(TypedTermList(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort()))) {
        // there may be already terms in the index
        for (const auto& t : iterTraits(tree->terms.iter())) {
          _rhsIndex.remove({ t, cl });
        }
        goto GOAL_CLAUSE;
      }
    }
    ALWAYS(clauseTrees.insert(cl, tree));
    return { ClauseStack(), _nonLinearityHandler.addNonGoalClause(cl) };
  }

  // If it is, it possibly contributes to some reachibility
  // trees, so we insert it as such
GOAL_CLAUSE:
  return addGoalClause(cl);
}

bool GoalReachabilityHandler::isTermSuperposable(Clause* cl, TypedTermList t) const
{
  ASS(!cl->isGoalClause());
  // TODO should we allow clauses not yet added to the handler? Check flow.
  auto ptr = clauseTrees.findPtr(cl);
  return ptr && iterTraits((*ptr)->nonGoalSuperposableTerms.iter())
    .any([t](TermList st) { return st.containsSubterm(t); });
}

std::pair<ClauseStack, ClauseTermPairs> GoalReachabilityHandler::addGoalClause(Clause* cl)
{
  ClauseStack resCls;
  ClauseTermPairs resPairs;

  ClauseStack todo;
  todo.push(cl);
  cl->makeGoalClause();

  DHSet<Clause*> nonGoalRemoved;
  // no need to add cl, as it has not been added yet
  // nonGoalRemoved.insert(cl);

  auto nonGoalRemoveFn = [&todo,&nonGoalRemoved](Clause* cl) {
    todo.push(cl);
    nonGoalRemoved.insert(cl);
  };

  while (todo.isNonEmpty()) {
    auto curr = todo.pop();

    // curr itself is becoming goal clause, so let's add it here
    resCls.push(curr);

    ASS_EQ(curr->length(),1);

    auto lit = (*curr)[0];
    ASS(lit->isEquality());

    DEBUG("adding goal clause ", *curr);

    // 1. Insert all strict subterms of the greater side into indices.
    // Note: this has to be done before step 2 below
    for (auto lhs : iterTraits(getLHSIterator(lit, ord))) {
      if (lhs.isVar()) { continue; }
      for (const auto& st : iterTraits(NonVariableNonTypeIterator(lhs.term(), /*includeSelf=*/lit->isNegative()))) {
        DEBUG("adding to goal lhs index ", *st);
        _goalSubtermIndex.insert({ st, lhs, lit, curr });
      }
    }

    // 2. Iterate reachibility trees
    ClauseTermPairs termsToAdd;

    for (auto lhs : iterTraits(getLHSIterator(lit, ord))) {
      if (lhs.isVar()) { continue; }
      TypedTermList rhs(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort());
      for (const auto& st : iterTraits(NonVariableNonTypeIterator(lhs.term(), /*includeSelf=*/lit->isNegative()))) {
        for (const auto& qr : iterTraits(_rhsIndex.getUnifications(st, /*retrieveSubstitutions=*/true))) {

          auto qcl = qr.data->clause;
          DEBUG("qcl ", *qcl);

          if (nonGoalRemoved.contains(qcl)) {
            continue;
          }

          if (lit->isNegative()) {
            nonGoalRemoveFn(qcl);
          } else {
            if (!ReachabilityTree::canBeAdded(rhs, *qr.unifier.ptr(), /*result=*/false)) {
              nonGoalRemoveFn(qcl);
            } else {
              termsToAdd.push({ qcl, qr.unifier->apply(rhs, /*result=*/false) });
            }
          }
        }
      }
    }

    // do this separately because the indices are modified
    while (termsToAdd.isNonEmpty()) {
      auto [qcl, t] = termsToAdd.pop();
      if (nonGoalRemoved.contains(qcl)) {
        continue;
      }
      auto& tree = clauseTrees.get(qcl);
      if (!tree->addTerm(t)) {
        nonGoalRemoveFn(qcl);
      }
    }
  }

  for (const auto& rcl : iterTraits(nonGoalRemoved.iter())) {

    ReachabilityTree* tree = nullptr;
    ALWAYS(clauseTrees.pop(rcl, tree));
    ASS_EQ(rcl, tree->cl);

    for (const auto& t : iterTraits(tree->terms.iter())) {
      _rhsIndex.remove({ t, rcl });
    }

    _nonLinearityHandler.removeNonGoalClause(rcl);

    delete tree;

    rcl->makeGoalClause();

    resPairs.loadFromIterator(_nonLinearityHandler.addGoalClause(rcl).iter());
  }

  resPairs.loadFromIterator(_nonLinearityHandler.addGoalClause(cl).iter());

  return { resCls, resPairs };
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
      continue;
    }

    handler._rhsIndex.insert({ curr, cl });

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

ClauseTermPairs GoalNonLinearityHandler::addNonGoalClause(Clause* cl)
{
  ASS(!cl->isGoalClause());

  ClauseTermPairs res;

  for (const auto& lit : cl->getSelectedLiteralIterator()) {
    for (auto lhs : iterTraits(getLHSIterator(lit, ord))) {
      for (const auto& t : iterTraits(NonVariableNonTypeIterator(lhs.term(), /*includeSelf=*/true))) {
        // handle equality lhs
        if (t == lhs && lit->isPositive()) {
          _nonGoalLHSIndex.handle(TermLiteralClause{ t, lit, cl }, /*adding=*/true);

          for (const auto& qr : iterTraits(_nonLinearGoalTermIndex.getUnifications(t, /*retrieveSubstitutions=*/false))) {
            perform(cl, qr.data->term, t, qr.data->constraints, res);
          }
        }
        _nonGoalSubtermIndex.handle(TermLiteralClause{ t, lit, cl }, /*adding=*/true);

        for (const auto& qr : iterTraits(_nonLinearGoalLHSIndex.getUnifications(t, /*retrieveSubstitutions=*/false))) {
          perform(cl, qr.data->term, t, qr.data->constraints, res);
        }
      }
    }
  }

  return res;
}

void GoalNonLinearityHandler::removeNonGoalClause(Clause* cl)
{
  ASS(!cl->isGoalClause());

  for (const auto& lit : cl->getSelectedLiteralIterator()) {
    for (auto lhs : iterTraits(getLHSIterator(lit, ord))) {
      for (const auto& t : iterTraits(NonVariableNonTypeIterator(lhs.term(), /*includeSelf=*/true))) {
        // handle equality lhs
        if (t == lhs && lit->isPositive()) {
          _nonGoalLHSIndex.handle(TermLiteralClause{ t, lit, cl }, /*adding=*/false);
        }
        _nonGoalSubtermIndex.handle(TermLiteralClause{ t, lit, cl }, /*adding=*/false);
      }
    }
  }
}

namespace {
  struct Linearizer : TermTransformer {
    Linearizer(unsigned nextVar, const DHMap<unsigned,TermList>& varSorts) : TermTransformer(true), nextVar(nextVar), varSorts(varSorts) {}
    TermList transformSubterm(TermList trm) override {
      if (trm.isVar() && !seen.insert(trm.var())) {
        auto sort = varSorts.get(trm.var());
        TypedTermList other(TermList::var(nextVar++), sort);
        constraints.emplace(TypedTermList(trm, sort), other);
        return other;
      }
      return trm;
    }
    LinearityConstraints constraints;
    DHSet<unsigned> seen;
    unsigned nextVar;
    const DHMap<unsigned,TermList>& varSorts;
  };
}

ClauseTermPairs GoalNonLinearityHandler::addGoalClause(Clause* cl)
{
  ASS(cl->isGoalClause());
  ClauseTermPairs res;

  DHMap<unsigned,TermList> varSorts;
  SortHelper::collectVariableSorts(const_cast<Clause*>(cl),varSorts);

  unsigned maxVar = 0;
  for (const auto& [v,s] : iterTraits(varSorts.items())) {
    maxVar = std::max(maxVar,v);
  }
  maxVar++;

  for (const auto& lit : cl->getSelectedLiteralIterator()) {
    for (auto lhs : iterTraits(getLHSIterator(lit, ord))) {
      if (lhs.isVar()) {
        _nonLinearGoalLHSIndex.handle(LinearTermLiteralClause{ lhs, LinearityConstraints(), lit, cl }, /*adding=*/true);
        _nonLinearGoalTermIndex.handle(LinearTermLiteralClause{ lhs, LinearityConstraints(), lit, cl }, /*adding=*/true);
        continue;
      }
      for (const auto& t : iterTraits(NonVariableNonTypeIterator(lhs.term(), /*includeSelf=*/true))) {
        Linearizer linearizer(maxVar, varSorts);
        auto lt = linearizer.transform(t);
        if (linearizer.constraints.isEmpty()) {
          continue;
        }
        // handle equality lhs
        if (t == lhs && lit->isPositive()) {
          _nonLinearGoalLHSIndex.handle(LinearTermLiteralClause{ lt, linearizer.constraints, lit, cl }, /*adding=*/true);

          for (const auto& qr : iterTraits(_nonGoalSubtermIndex.getUnifications(lt, /*retrieveSubstitutions=*/false))) {
            perform(qr.data->clause, lt, qr.data->term, linearizer.constraints, res);
          }
        }
        _nonLinearGoalTermIndex.handle(LinearTermLiteralClause{ lt, linearizer.constraints, lit, cl }, /*adding=*/true);

        for (const auto& qr : iterTraits(_nonGoalLHSIndex.getUnifications(lt, /*retrieveSubstitutions=*/false))) {
          perform(qr.data->clause, lt, qr.data->term, linearizer.constraints, res);
        }
      }
    }
  }

  return res;
}

void GoalNonLinearityHandler::perform(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm, const LinearityConstraints& cons, ClauseTermPairs& res)
{
  // TODO maybe put this somewhere else
  if (ngcl->isGoalClause()) {
    return;
  }
  ASS(goalTerm.isTerm());
  ASS(nonGoalTerm.isTerm());

  DHMap<unsigned, TermList> map;

  SubtermIterator goalIt(goalTerm.term());
  SubtermIterator nonGoalIt(nonGoalTerm.term());

  while (goalIt.hasNext()) {
    ALWAYS(nonGoalIt.hasNext());
    auto goalSt = goalIt.next();
    auto nonGoalSt = nonGoalIt.next();

    if (goalSt.isVar()) {
      ALWAYS(map.insert(goalSt.var(), nonGoalSt));
      nonGoalIt.right();
    } else if (nonGoalSt.isVar()) {
      goalIt.right();
    }
  }
  ASS(!nonGoalIt.hasNext());

  for (const auto& [x,y] : cons) {
    ASS(x.isVar());
    ASS(y.isVar());
    auto xptr = map.findPtr(x.var());
    auto yptr = map.findPtr(y.var());
    // TODO find out if this is really correct
    if (!xptr || !yptr) {
      continue;
    }
    auto xS = *xptr;
    auto yS = *yptr;
    // TODO handle non-ground terms
    if (xS != yS && xS.isTerm() && yS.isTerm()) {
      DEBUG("found pair ", x, " != ", y, " (", xS, " != ", yS, ")");
      DEBUG("for ", *ngcl);
      auto tree = handler.clauseTrees.get(ngcl);
      if (tree->nonGoalSuperposableTerms.insert(xS.term())) {
        res.emplace(ngcl, xS.term());
        DEBUG("could insert ", xS);
      }
      if (tree->nonGoalSuperposableTerms.insert(yS.term())) {
        res.emplace(ngcl, yS.term());
        DEBUG("could insert ", yS);
      }
    }
  }
}