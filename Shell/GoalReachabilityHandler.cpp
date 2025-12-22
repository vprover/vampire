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

constexpr unsigned kMaxChainLength = 2;

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

bool isRenamingOn(TypedTermList t, ResultSubstitution& subst, bool result)
{
  if (t.isEmpty()) {
    return true;
  }

  DEBUG("isRenamingOn ", t.untyped(), " ", subst.apply(t, result).untyped());

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
      return false;
    }
  }
  return true;
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

void collectVariableSorts(TypedTermList t, DHMap<unsigned,TermList>& varSorts)
{
  if (t.isVar()) {
    if (!varSorts.insert(t.var(), t.sort())) {
      ASS_EQ(t.sort(), varSorts.get(t.var()));
    }
  } else {
    SortHelper::collectVariableSorts(t.term(),varSorts);
  }
}

Chain::Chain(TypedTermList lhs, TypedTermList rhs, unsigned length, bool isBase)
  : lhs(lhs), rhs(rhs), length(length), isBase(isBase)
{
  // ASS_EQ(rhs.isEmpty(), !length);

  DHMap<unsigned,TermList> varSorts;
  collectVariableSorts(lhs, varSorts);
  if (rhs.isNonEmpty()) {
    collectVariableSorts(rhs, varSorts);
  }

  unsigned maxVar = 0;
  for (const auto& [v,s] : iterTraits(varSorts.items())) {
    maxVar = std::max(maxVar,v);
  }
  maxVar++;

  if (lhs.isVar()) {
    linearLhs = lhs;
  } else {
    Linearizer linearizer(maxVar, varSorts);
    linearLhs = linearizer.transform(lhs.term());
    constraints = linearizer.constraints;
  }
}

Literal* assertUnitEquality(Clause* cl) {
  if (cl->length() != 1) {
    INVALID_OPERATION("only unit clauses are supported");
  }

  auto lit = (*cl)[0];
  if (!lit->isEquality()) {
    INVALID_OPERATION("only equality is supported");
  }
  return lit;
}

void GoalReachabilityHandler::addClause(Clause* cl)
{
  DEBUG("addClause ", *cl);
  auto lit = assertUnitEquality(cl);

  _newSuperposableTerms.reset();
  _newGoalClauses.reset();
  ASS(_newChainsToHandle.isEmpty());

  // Try adding it as non-goal clause
  if (lit->isPositive() && tryAddNonGoalClause(cl)) {
    ASS(_newGoalClauses.isEmpty());
    return;
  }

  // If it is, it possibly contributes to reachibility of other clauses
  addGoalClause(cl);
  handleNewChains();
}

bool GoalReachabilityHandler::isTermSuperposable(Clause* cl, TypedTermList t) const
{
  ASS(!cl->isGoalClause());
  // TODO should we allow clauses not yet added to the handler? Check flow.
  auto ptr = _superposableTerms.findPtr(cl);
  return ptr && iterTraits(ptr->iter()).any([t](Term* st) { return st->containsSubterm(t); });
}

// combine (left) l -> r and (right) s[r'] -> t into lσ -> tσ where σ = mgu(r,r')
Chain* combineChains(Chain* left, Chain* right, TypedTermList t, ResultSubstitution& subst, bool leftIsResult)
{
  DEBUG("combining chains ", *left, " and ", *right, " in subterm ", t);

  ASS(right->isBase);

  auto lhs = subst.apply(left->lhs, leftIsResult);
  TypedTermList rhs;
  if (right->rhs.isNonEmpty()) {
    rhs = subst.apply(right->rhs, !leftIsResult);
  }
  auto length = left->length+right->length;
  if (length > kMaxChainLength) {
    return nullptr;
  }
  if (left->lhs == lhs && left->rhs == rhs) {
    return nullptr;
  }
  return new Chain(lhs, rhs, length, /*isBase=*/false);
}

void GoalReachabilityHandler::addGoalClause(Clause* cl)
{
  DEBUG("addGoalClause ", *cl);
  auto lit = assertUnitEquality(cl);

  ASS(!cl->isGoalClause());
  cl->makeGoalClause();
  _newGoalClauses.push(cl);

  for (auto lhs : iterTraits(getLHSIterator(lit, ord))) {
    auto rhs = lit->isNegative() ? TypedTermList() : TypedTermList(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort());
    auto length = lit->isNegative() ? 0 : 1;
    auto chain = new Chain(lhs, rhs, length, /*isBase=*/true);
    _newChainsToHandle.push(chain);

    // only add these length-1 chains to avoid explosion of chains
    if (lhs.isTerm()) {
      // insert into forward chaining index
      for (const auto& t : iterTraits(NonVariableNonTypeIterator(lhs.term(), /*includeSelf=*/lit->isNegative()))) {
        _nonlinearChainSubtermIndex.handle(TermChain{ t, chain }, /*insert=*/true);
      }

      // perform backward chaining: combine (result) l -> r and (query) s[r'] -> t into lσ -> tσ where σ = mgu(r,r')
      for (const auto& t : iterTraits(NonVariableNonTypeIterator(chain->lhs.term(), /*includeSelf=*/chain->length==0))) {
        for (const auto& qr : iterTraits(_chainRHSIndex.getUnifications(t, /*retrieveSubstitutions=*/true))) {
          _newChainsToHandle.push(combineChains(qr.data->chain, chain, t, *qr.unifier.ptr(), /*leftIsResult=*/true));
        }
      }

      // add to non-linearity handler
      _nonLinearityHandler.addChain(chain);
    }
  }
}

void GoalReachabilityHandler::handleNewChains()
{
  while (_newChainsToHandle.isNonEmpty()) {

    auto curr = _newChainsToHandle.pop();

    if (!curr) {
      continue;
    }

    // 1. insert chain into indices
    // variables do not need to be inserted into the subterm indices
    DEBUG("adding chain ", *curr);
    if (curr->lhs.isTerm()) {
      for (const auto& t : iterTraits(NonVariableNonTypeIterator(curr->linearLhs.term(), /*includeSelf=*/curr->length==0))) {
        _linearChainSubtermIndex.handle(TermChain{ t, curr }, /*insert=*/true);
      }
    }
    if (curr->rhs.isNonEmpty()) {
      _chainRHSIndex.insert(TermChain{ curr->rhs, curr });
    }

    // 2. get unifications with non-goal rhss
    DHSet<Clause*> reached;
    if (curr->lhs.isTerm()) {
      for (const auto& t : iterTraits(NonVariableNonTypeIterator(curr->linearLhs.term(), /*includeSelf=*/curr->length==0))) {
        for (const auto& qr : iterTraits(_nonGoalRHSIndex.getUnifications(t, /*retrieveSubstitutions=*/true))) {
          if (isReached(qr.data->clause, qr.data->term, t, curr, *qr.unifier.ptr(), /*result=*/false)) {
            reached.insert(qr.data->clause);
          }
        }
      }
    }

    for (const auto& rcl : iterTraits(reached.iter())) {
      handleNonGoalClause(rcl, /*insert=*/false);
      _nonLinearityHandler.removeNonGoalClause(rcl);
      addGoalClause(rcl);
    }

    // 3. build new chains, i.e. get unifications with goal rhss and lhss
    for (auto&& newChain : buildNewChains(curr)) {
      _newChainsToHandle.push(newChain);
    }
  }
}

bool GoalReachabilityHandler::isReached(
  Clause* ngCl, TypedTermList ngRhs, TypedTermList gSubterm, const Chain* chain, ResultSubstitution& subst, bool result)
{
  auto clauseTermPairs = GoalNonLinearityHandler::get(ngCl, gSubterm, ngRhs, chain->constraints);
  if (clauseTermPairs.isNonEmpty()) {
    for (auto [ngcl, t] : clauseTermPairs) {
      addSuperposableTerm(ngcl, t);
    }
    return false;
  }

  if (isRenamingOn(chain->rhs, subst, result)) {
    DEBUG("reached ", *ngCl, " with ", *chain, " unifying ", ngRhs, " with ", gSubterm);
    return true;
  }
  if (chain->length == kMaxChainLength) {
    DEBUG("max chain length reached for ", *ngCl, " with ", *chain);
    return true;
  }
  return false;
}

bool GoalReachabilityHandler::tryAddNonGoalClause(Clause* cl)
{
  DEBUG("tryAddNonGoalClause ", *cl);
  auto lit = assertUnitEquality(cl);

  if (lit->isNegative()) {
    return false;
  }

  for (const auto& lhs : iterTraits(getLHSIterator(lit, ord))) {
    TypedTermList rhs(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort());
    for (const auto& qr : iterTraits(_linearChainSubtermIndex.getUnifications(rhs, /*retrieveSubstitutions=*/true))) {
      if (isReached(cl, rhs, qr.data->term, qr.data->chain, *qr.unifier.ptr(), /*result=*/true)) {
        return false;
      }
    }
  }

  // insert as non-goal clause
  for (const auto& lhs : iterTraits(getLHSIterator(lit, ord))) {
    _nonGoalRHSIndex.insert({ TypedTermList(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort()), lit, cl });
  }

  _nonLinearityHandler.addNonGoalClause(cl);

  return true;
}

Stack<Chain*> GoalReachabilityHandler::buildNewChains(Chain* chain)
{
  Stack<Chain*> res;

  // forward: (query) l -> r and (result) s[r'] -> t into lσ -> tσ where σ = mgu(r,r')
  if (chain->rhs.isNonEmpty()) {
    for (const auto& qr : iterTraits(_nonlinearChainSubtermIndex.getUnifications(chain->rhs, /*retrieveSubstitutions=*/true))) {
      res.push(combineChains(chain, qr.data->chain, qr.data->term, *qr.unifier.ptr(), /*leftIsResult=*/false));
    }
  }

  // backward: (result) l -> r and (query) s[r'] -> t into lσ -> tσ where σ = mgu(r,r')
  if (chain->isBase && chain->lhs.isTerm()) {
    for (const auto& t : iterTraits(NonVariableNonTypeIterator(chain->lhs.term(), /*includeSelf=*/chain->length==0))) {
      for (const auto& qr : iterTraits(_chainRHSIndex.getUnifications(t, /*retrieveSubstitutions=*/true))) {
        res.push(combineChains(qr.data->chain, chain, t, *qr.unifier.ptr(), /*leftIsResult=*/true));
      }
    }
  }

  return res;
}

void GoalReachabilityHandler::handleNonGoalClause(Clause* cl, bool insert)
{
  auto lit = assertUnitEquality(cl);

  ASS(lit->isPositive());
  ASS(!cl->isGoalClause());

  for (const auto& lhs : iterTraits(getLHSIterator(lit, ord))) {
    _nonGoalRHSIndex.handle({ TypedTermList(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort()), lit, cl }, insert);
  }
}

// GoalNonLinearityHandler

void GoalNonLinearityHandler::addNonGoalClause(Clause* cl)
{
  DEBUG("linearity addNonGoalClause ", *cl);
  auto lit = assertUnitEquality(cl);
  ASS(!cl->isGoalClause());

  for (auto lhs : iterTraits(getLHSIterator(lit, ord))) {
    for (const auto& t : iterTraits(NonVariableNonTypeIterator(lhs.term(), /*includeSelf=*/true))) {
      // handle equality lhs
      if (t == lhs && lit->isPositive()) {
        _nonGoalLHSIndex.handle(TermLiteralClause{ t, lit, cl }, /*insert=*/true);

        for (const auto& qr : iterTraits(_nonLinearGoalTermIndex.getUnifications(t, /*retrieveSubstitutions=*/false))) {
          perform(cl, qr.data->term, t, qr.data->chain->constraints);
        }
      }
      _nonGoalSubtermIndex.handle(TermLiteralClause{ t, lit, cl }, /*insert=*/true);

      for (const auto& qr : iterTraits(_nonLinearGoalLHSIndex.getUnifications(t, /*retrieveSubstitutions=*/false))) {
        perform(cl, qr.data->term, t, qr.data->chain->constraints);
      }
    }
  }
}

void GoalNonLinearityHandler::removeNonGoalClause(Clause* cl)
{
  ASS(!cl->isGoalClause());
  auto lit = assertUnitEquality(cl);

  for (auto lhs : iterTraits(getLHSIterator(lit, ord))) {
    for (const auto& t : iterTraits(NonVariableNonTypeIterator(lhs.term(), /*includeSelf=*/true))) {
      // handle equality lhs
      if (t == lhs && lit->isPositive()) {
        _nonGoalLHSIndex.handle(TermLiteralClause{ t, lit, cl }, /*insert=*/false);
      }
      _nonGoalSubtermIndex.handle(TermLiteralClause{ t, lit, cl }, /*insert=*/false);
    }
  }
}

void GoalNonLinearityHandler::addChain(Chain* chain)
{
  DEBUG("linearity addChain ", *chain);
  ASS(chain->isBase);

  _nonLinearGoalLHSIndex.handle(TermChain{ chain->linearLhs, chain }, /*insert=*/true);

  for (const auto& qr : iterTraits(_nonGoalSubtermIndex.getUnifications(chain->linearLhs, /*retrieveSubstitutions=*/false))) {
    perform(qr.data->clause, chain->linearLhs, qr.data->term, chain->constraints);
  }

  for (const auto& t : iterTraits(NonVariableNonTypeIterator(chain->linearLhs.term(), /*includeSelf=*/true))) {
    _nonLinearGoalTermIndex.handle(TermChain{ t, chain }, /*insert=*/true);

    for (const auto& qr : iterTraits(_nonGoalLHSIndex.getUnifications(t, /*retrieveSubstitutions=*/false))) {
      perform(qr.data->clause, t, qr.data->term, chain->constraints);
    }
  }
}

ClauseTermPairs GoalNonLinearityHandler::get(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm, const LinearityConstraints& cons)
{
  ASS(!ngcl->isGoalClause());
  if (cons.isEmpty() || nonGoalTerm.isVar()) {
    return ClauseTermPairs();
  }
  ASS(goalTerm.isTerm());

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

  ClauseTermPairs res;

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
      res.emplace(ngcl, xS.term());
      res.emplace(ngcl, yS.term());
    }
  }
  return res;
}

void GoalNonLinearityHandler::perform(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm, const LinearityConstraints& cons)
{
  // TODO maybe put this somewhere else
  if (ngcl->isGoalClause()) {
    return;
  }
  ASS(goalTerm.isTerm());
  ASS(nonGoalTerm.isTerm());

  for (auto [cl, t] : get(ngcl, goalTerm, nonGoalTerm, cons)) {
    handler.addSuperposableTerm(ngcl, t);
  }
}

void GoalReachabilityHandler::addSuperposableTerm(Clause* ngcl, Term* t)
{
  DHSet<Term*>* ptr;
  _superposableTerms.getValuePtr(ngcl, ptr);
  if (ptr->insert(t)) {
    _newSuperposableTerms.emplace(ngcl, t);
    DEBUG("could insert ", t, " for ", *ngcl);
  }
}