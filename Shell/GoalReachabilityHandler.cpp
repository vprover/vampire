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

Chain::Chain(TypedTermList lhs, TypedTermList rhs, unsigned length)
  : lhs(lhs), rhs(rhs), length(length)
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

std::pair<ClauseStack, ClauseTermPairs> GoalReachabilityHandler::addClause(Clause* cl)
{
  DEBUG("addClause ", *cl);
  auto lit = assertUnitEquality(cl);

  // We check whether the clause is a goal clause or not.

  // It is a goal clause if the literal is negative
  if (lit->isNegative()) {
    goto GOAL_CLAUSE;
  }

  {
    ClauseTermPairs resPairs;
    if (addNonGoalClause(cl, resPairs)) {
      resPairs.loadFromIterator(_nonLinearityHandler.addNonGoalClause(cl).iter());
      return { ClauseStack(), resPairs };
    }
  }

  // If it is, it possibly contributes to reachibility of other clauses
GOAL_CLAUSE:
  return addGoalClause(cl);
}

bool GoalReachabilityHandler::isTermSuperposable(Clause* cl, TypedTermList t) const
{
  ASS(!cl->isGoalClause());
  // TODO should we allow clauses not yet added to the handler? Check flow.
  auto ptr = _superposableTerms.findPtr(cl);
  return ptr && iterTraits(ptr->iter()).any([t](Term* st) { return st->containsSubterm(t); });
}

std::pair<ClauseStack, ClauseTermPairs> GoalReachabilityHandler::addGoalClause(Clause* cl)
{
  DEBUG("addGoalClause ", *cl);
  assertUnitEquality(cl);

  cl->makeGoalClause();

  ClauseStack resCls { cl };
  ClauseTermPairs resPairs;

  resPairs.loadFromIterator(_nonLinearityHandler.addGoalClause(cl).iter());

  auto todo = Stack<Chain*>::fromIterator(insertGoalClause(cl).iter());

  while (todo.isNonEmpty()) {

    auto curr = todo.pop();

    if (!curr) {
      continue;
    }

    // 1. add to indices
    addChain(curr);

    // 2. get unifications with non-goal rhss
    auto [cls, pairs] = checkNonGoalReachability(curr);
    // TODO remove cls from indices and add them to todo as new chains
    for (const auto& rcl : cls) {
      resCls.push(rcl);

      handleNonGoalClause(rcl, /*insert=*/false);
      _nonLinearityHandler.removeNonGoalClause(rcl);

      rcl->makeGoalClause();

      todo.loadFromIterator(insertGoalClause(rcl).iter());
      resPairs.loadFromIterator(_nonLinearityHandler.addGoalClause(rcl).iter());
    }
    resPairs.loadFromIterator(pairs.iter());

    // 3. build new chains, i.e. get unifications with goal rhss and lhss
    for (auto&& newChain : buildNewChains(curr)) {
      todo.push(newChain);
    }
  }
  return { resCls, resPairs };
}

bool GoalReachabilityHandler::addNonGoalClause(Clause* cl, ClauseTermPairs& resPairs)
{
  DEBUG("addNonGoalClause ", *cl);
  auto lit = assertUnitEquality(cl);

  if (lit->isNegative()) {
    return false;
  }

  for (const auto& lhs : iterTraits(getLHSIterator(lit, ord))) {
    TypedTermList rhs(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort());
    for (const auto& qr : iterTraits(_linearChainSubtermIndex.getUnifications(rhs, /*retrieveSubstitutions=*/true))) {

      auto clauseTermPairs = GoalNonLinearityHandler::perform(cl, qr.data->term, rhs, qr.data->chain->constraints);
      if (clauseTermPairs.isNonEmpty()) {
        for (auto [ngcl, t] : clauseTermPairs) {
          DHSet<Term*>* ptr;
          _superposableTerms.getValuePtr(ngcl, ptr);
          if (ptr->insert(t.term())) {
            resPairs.emplace(ngcl, t);
            DEBUG("could insert ", t, " for ", *ngcl);
          }
        }
      } else {
        if (isRenamingOn(qr.data->chain->rhs, *qr.unifier.ptr(), /*result=*/true)) {
          DEBUG("reached ", *cl, " with ", *qr.data->chain, " unifying ", rhs, " with ", qr.data->term);
          return false;
        }
        if (qr.data->chain->length == kMaxChainLength) {
          DEBUG("max chain length reached for ", *cl, " with ", *qr.data->chain);
          return false;
        }
      }
    }
  }

  // insert as non-goal clause
  for (const auto& lhs : iterTraits(getLHSIterator(lit, ord))) {
    _nonGoalRHSIndex.insert({ TypedTermList(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort()), lit, cl });
  }

  return true;
}

void GoalReachabilityHandler::addChain(Chain* chain)
{
  DEBUG("adding chain ", *chain);

  // variables do not need to be inserted into the subterm indices
  if (chain->lhs.isTerm()) {
    for (const auto& t : iterTraits(NonVariableNonTypeIterator(chain->lhs.term(), /*includeSelf=*/chain->isLengthZero()))) {
      _nonlinearChainSubtermIndex.handle(TermChain{ t, chain }, /*insert=*/true);
    }
    for (const auto& t : iterTraits(NonVariableNonTypeIterator(chain->linearLhs.term(), /*includeSelf=*/chain->isLengthZero()))) {
      _linearChainSubtermIndex.handle(TermChain{ t, chain }, /*insert=*/true);
    }
  }
}

std::pair<ClauseStack, ClauseTermPairs> GoalReachabilityHandler::checkNonGoalReachability(Chain* chain)
{
  DHSet<Clause*> reached;

  if (chain->lhs.isVar()) {
    return std::pair<ClauseStack, ClauseTermPairs>();
  }

  ClauseTermPairs resPairs;

  for (const auto& t : iterTraits(NonVariableNonTypeIterator(chain->linearLhs.term(), /*includeSelf=*/chain->isLengthZero()))) {
    for (const auto& qr : iterTraits(_nonGoalRHSIndex.getUnifications(t, /*retrieveSubstitutions=*/true))) {

      auto clauseTermPairs = GoalNonLinearityHandler::perform(qr.data->clause, t, qr.data->term, chain->constraints);
      if (clauseTermPairs.isNonEmpty()) {
        for (auto [ngcl, t] : clauseTermPairs) {
          DHSet<Term*>* ptr;
          _superposableTerms.getValuePtr(ngcl, ptr);
          if (ptr->insert(t.term())) {
            resPairs.emplace(ngcl, t);
            DEBUG("could insert ", t, " for ", *ngcl);
          }
        }
      } else {
        if (isRenamingOn(chain->rhs, *qr.unifier.ptr(), /*result=*/false)) {
          DEBUG("reached ", *qr.data->clause, " with ", *chain, " unifying ", qr.data->term, " with ", *t);
          reached.insert(qr.data->clause);
        }
        if (chain->length == kMaxChainLength) {
          DEBUG("max chain length reached for ", *qr.data->clause, " with ", *chain);
          reached.insert(qr.data->clause);
        }
      }
    }
  }

  return { ClauseStack::fromIterator(reached.iter()), resPairs };
}

// combine (left) l -> r and (right) s[r'] -> t into lσ -> tσ where σ = mgu(r,r')
Chain* combineChains(Chain* left, Chain* right, TypedTermList t, ResultSubstitution& subst, bool leftIsResult)
{
  DEBUG("combining chains ", *left, " and ", *right, " in subterm ", t);

  ASS(left->isLengthOne());

  auto lhs = subst.apply(left->lhs, leftIsResult);
  TypedTermList rhs;
  if (!right->isBase()) {
    rhs = subst.apply(right->rhs, !leftIsResult);
  }
  auto length = left->length+right->length;
  if (length > kMaxChainLength) {
    return nullptr;
  }
  if (left->lhs == lhs && left->rhs == rhs) {
    return nullptr;
  }
  return new Chain(lhs, rhs, length);
}

Stack<Chain*> GoalReachabilityHandler::buildNewChains(Chain* chain)
{
  Stack<Chain*> res;

  // forward: (result) l -> r and (query) s[r'] -> t into lσ -> tσ where σ = mgu(r,r')
  if (chain->lhs.isTerm()) {
    for (const auto& t : iterTraits(NonVariableNonTypeIterator(chain->lhs.term(), /*includeSelf=*/chain->isLengthZero()))) {
      for (const auto& qr : iterTraits(_chainRHSIndex.getUnifications(t, /*retrieveSubstitutions=*/true))) {
        res.push(combineChains(qr.data->chain, chain, t, *qr.unifier.ptr(), /*leftIsResult=*/true));
      }
    }
  }

  // backward: (query) l -> r and (result) s[r'] -> t into lσ -> tσ where σ = mgu(r,r')
  if (chain->isLengthOne() && !chain->isBase()) {
    for (const auto& qr : iterTraits(_nonlinearChainSubtermIndex.getUnifications(chain->rhs, /*retrieveSubstitutions=*/true))) {
      res.push(combineChains(chain, qr.data->chain, qr.data->term, *qr.unifier.ptr(), /*leftIsResult=*/false));
    }
  }

  return res;
}

Stack<Chain*> GoalReachabilityHandler::insertGoalClause(Clause* cl)
{
  auto lit = assertUnitEquality(cl);

  ASS(cl->isGoalClause());

  Stack<Chain*> res;

  for (const auto& lhs : iterTraits(getLHSIterator(lit, ord))) {
    if (lit->isNegative()) {
      res.push(new Chain(lhs, TypedTermList(), 0));
    } else {
      auto chain = new Chain(lhs, TypedTermList(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort()), 1);
      res.push(chain);
      // only add these length-1 chains to avoid explosion of chains
      _chainRHSIndex.insert(TermChain{ chain->rhs, chain });
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

ClauseTermPairs GoalNonLinearityHandler::addNonGoalClause(Clause* cl)
{
  DEBUG("linearity addNonGoalClause ", *cl);
  auto lit = assertUnitEquality(cl);
  ASS(!cl->isGoalClause());

  ClauseTermPairs res;

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

  return res;
}

void GoalNonLinearityHandler::removeNonGoalClause(Clause* cl)
{
  ASS(!cl->isGoalClause());
  auto lit = assertUnitEquality(cl);

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

ClauseTermPairs GoalNonLinearityHandler::addGoalClause(Clause* cl)
{
  DEBUG("linearity addGoalClause ", *cl);
  auto lit = assertUnitEquality(cl);

  ASS(cl->isGoalClause());
  ClauseTermPairs res;

  DHMap<unsigned,TermList> varSorts;
  SortHelper::collectVariableSorts(const_cast<Clause*>(cl),varSorts);

  unsigned maxVar = 0;
  for (const auto& [v,s] : iterTraits(varSorts.items())) {
    maxVar = std::max(maxVar,v);
  }
  maxVar++;

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

  return res;
}

ClauseTermPairs GoalNonLinearityHandler::perform(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm, const LinearityConstraints& cons)
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

void GoalNonLinearityHandler::perform(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm, const LinearityConstraints& cons, ClauseTermPairs& resPairs)
{
  // TODO maybe put this somewhere else
  if (ngcl->isGoalClause()) {
    return;
  }
  ASS(goalTerm.isTerm());
  ASS(nonGoalTerm.isTerm());

  for (auto [cl, t] : perform(ngcl, goalTerm, nonGoalTerm, cons)) {
    DHSet<Term*>* ptr;
    handler._superposableTerms.getValuePtr(ngcl, ptr);
    if (ptr->insert(t.term())) {
      resPairs.emplace(ngcl, t.term());
      DEBUG("could insert ", t, " for ", *ngcl);
    }
  }
}