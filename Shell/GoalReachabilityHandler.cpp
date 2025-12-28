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
#include "Kernel/EqHelper.hpp"
#include "Kernel/TermTransformer.hpp"

using namespace Shell;
using namespace Kernel;

#define DEBUG(...) // DBG(__VA_ARGS__)

// This is different from EqHelper::getSuperpositionLHSIterator because it works for negative equalities too
auto lhsIter(Literal* lit, const Ordering& ord)
{
  ASS(lit->isEquality());
  auto sort = SortHelper::getEqualityArgumentSort(lit);
  auto lhs = lit->termArg(0);
  auto rhs = lit->termArg(1);
  switch (ord.getEqualityArgumentOrder(lit)) {
    case Ordering::INCOMPARABLE:
      return iterItems(TypedTermList(lhs, sort), TypedTermList(rhs, sort));
    case Ordering::GREATER:
      return iterItems(TypedTermList(lhs, sort));
    case Ordering::LESS:
      return iterItems(TypedTermList(rhs, sort));
    //there should be no equality literals of equal terms
    default:
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

Chain::Chain(TypedTermList origLhs, TypedTermList lhs, TypedTermList rhs, unsigned length, bool isBase)
  : origLhs(origLhs), lhs(lhs), rhs(rhs), length(length), isBase(isBase)
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

  env.statistics->numberOfChains++;
  if (length > env.statistics->maxChainLength) {
    env.statistics->maxChainLength = length;
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

bool GoalReachabilityHandler::isTermSuperposable(Clause* cl, TypedTermList t) const
{
  ASS(!cl->isGoalClause());
  // TODO should we allow clauses not yet added to the handler? Check flow.
  auto ptr = _superposableTerms.findPtr(cl);
  return ptr && iterTraits(ptr->iter()).any([t](Term* st) { return st->containsSubterm(t); });
}

// combine (left) l -> r and (right) s[r'] -> t into lσ -> tσ where σ = mgu(r,r')
Chain* GoalReachabilityHandler::combineChains(Chain* left, Chain* right, TypedTermList t, ResultSubstitution& subst, bool leftIsResult)
{
  DEBUG("combining chains ", *left, " and ", *right, " in subterm ", t.untyped());

  ASS(right->isBase);

  auto lhs = subst.apply(left->lhs, leftIsResult);
  TypedTermList rhs;
  if (right->rhs.isNonEmpty()) {
    rhs = subst.apply(right->rhs, !leftIsResult);
  }
  auto length = left->length+right->length;
  // if (length > _chainLimit) {
  //   return nullptr;
  // }
  if (left->lhs == lhs && left->rhs == rhs) {
    return nullptr;
  }
  return new Chain(left->origLhs, lhs, rhs, length, /*isBase=*/false);
}

void GoalReachabilityHandler::addGoalClause(Clause* cl)
{
  DEBUG("addGoalClause ", *cl);
  auto lit = assertUnitEquality(cl);

  ASS(!cl->isGoalClause());
  cl->makeGoalClause();
  _newGoalClauses.push(cl);
  Stack<Chain*>* ptr;
  ALWAYS(_chainMap.getValuePtr(cl, ptr));

  for (auto lhs : lhsIter(lit, _ord)) {
    auto rhs = lit->isNegative() ? TypedTermList() : TypedTermList(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort());
    auto length = lit->isNegative() ? 0 : 1;
    auto chain = new Chain(lhs, lhs, rhs, length, /*isBase=*/true);

    // associate chain with clause
    ptr->push(chain);

    // insert into indices
    handleBaseChain(chain, /*insert=*/true);

    if (lhs.isTerm()) {
      // perform backward chaining: combine (result) l -> r and (query) s[r'] -> t into lσ -> tσ where σ = mgu(r,r')
      for (const auto& t : iterTraits(NonVariableNonTypeIterator(chain->lhs.term(), /*includeSelf=*/chain->length==0))) {
        for (const auto& qr : iterTraits(_chainRHSIndex.getUnifications(t, /*retrieveSubstitutions=*/true))) {
          _newChainsToHandle.push_back(combineChains(qr.data->chain, chain, t, *qr.unifier.ptr(), /*leftIsResult=*/true));
        }
      }
    }
    // add to chains to be handled
    _newChainsToHandle.push_back(chain);
  }
}

bool GoalReachabilityHandler::iterate()
{
  DEBUG("iterate");

  unsigned cnt = 0;

  while (_newChainsToHandle.isNonEmpty()) {

    // uncomment this to enable dovetailing
    if (cnt++ >= _chainLimit) {
      return false;
    }

    auto curr = _newChainsToHandle.pop_front();

    if (!curr) {
      continue;
    }

    ASS(!curr->expanded);

    // 1. get unifications with non-goal rhss
    bool expand = false;
    DHSet<Clause*> reached;
    if (curr->lhs.isTerm()) {

      if (curr->length == 0) {
        for (const auto& qr : iterTraits(_nonGoalRHSIndex.getUnifications(curr->linearLhs.term(), /*retrieveSubstitutions=*/true))) {
          if (isReached(qr.data->clause, qr.data->term, curr->linearLhs.term(), curr, *qr.unifier.ptr(), /*goalIsResult=*/false)) {
            reached.insert(qr.data->clause);
          }
          expand = true;
        }
      }
      SubtermIterator itO(curr->origLhs.term());
      SubtermIterator itL(curr->linearLhs.term());
      while (itO.hasNext()) {
        ALWAYS(itL.hasNext());
        auto tO = itO.next();
        auto tL = itL.next();
        if (tO.isVar()) {
          itL.right();
          continue;
        }
        if (tL.isVar()) {
          continue;
        }
        for (const auto& qr : iterTraits(_nonGoalRHSIndex.getUnifications(tL.term(), /*retrieveSubstitutions=*/true))) {
          if (isReached(qr.data->clause, qr.data->term, tL.term(), curr, *qr.unifier.ptr(), /*goalIsResult=*/false)) {
            reached.insert(qr.data->clause);
          }
          expand = true;
        }
      }

      // for (const auto& t : iterTraits(NonVariableNonTypeIterator(curr->linearLhs.term(), /*includeSelf=*/curr->length==0))) {
      //   for (const auto& qr : iterTraits(_nonGoalRHSIndex.getUnifications(t, /*retrieveSubstitutions=*/true))) {
      //     if (isReached(qr.data->clause, qr.data->term, t, curr, *qr.unifier.ptr(), /*goalIsResult=*/false)) {
      //       reached.insert(qr.data->clause);
      //     }
      //     expand = true;
      //   }
      // }
    }

    // 2. insert chain into indices
    handleChain(curr, expand, /*insert=*/true);

    // 4. add clauses that have been reached as goal clauses
    for (const auto& rcl : iterTraits(reached.iter())) {
      handleNonGoalClause(rcl, /*insert=*/false);
      addGoalClause(rcl);
    }

    // 5. build new chains if needed, i.e. get unifications with goal rhss and lhss
    if (expand) {
      for (auto&& newChain : chainForward(curr)) {
        _newChainsToHandle.push_back(newChain);
      }
      curr->expanded = true;
    }
  }

  return true;
}

bool GoalReachabilityHandler::isReached(
  Clause* ngCl, TypedTermList ngRhs, TypedTermList gSubterm, const Chain* chain, ResultSubstitution& subst, bool goalIsResult)
{
  BacktrackData btd;
  subst.bdRecord(btd);
  auto clauseTermPairs = _nonLinearityHandler.get(ngCl, gSubterm, ngRhs, chain->constraints, subst, goalIsResult);
  if (clauseTermPairs.isNonEmpty()) {
    for (auto [ngcl, t] : clauseTermPairs) {
      addSuperposableTerm(ngcl, t);
    }
    btd.backtrack();
    subst.bdDone();
    return false;
  }

  if (isRenamingOn(chain->rhs, subst, goalIsResult)) {
    DEBUG("reached ", *ngCl, " with ", *chain, " unifying ", ngRhs.untyped(), " with ", gSubterm.untyped());
    btd.backtrack();
    subst.bdDone();
    return true;
  }
  btd.backtrack();
  subst.bdDone();
  // if (chain->length == _chainLimit) {
  //   DEBUG("max chain length reached for ", *ngCl, " with ", *chain);
  //   return true;
  // }
  return false;
}

GoalReachabilityHandler::GoalReachabilityHandler(SaturationAlgorithm& salg)
  : _ord(salg.getOrdering()),
    _chainLimit(salg.getOptions().goalOrientedChainLimit()),
    _nonLinearityHandler(salg, *this)
{}

void GoalReachabilityHandler::addClause(Clause* cl)
{
  DEBUG("addClause ", *cl);
  auto lit = assertUnitEquality(cl);

  // for now we must ensure that these hold
  ASS(_newSuperposableTerms.isEmpty());
  ASS(_newGoalClauses.isEmpty());
  // ASS(_newChainsToHandle.isEmpty());

  if (lit->isNegative()) {
    addGoalClause(cl);
    return;
  }

  DHSet<Chain*> toExpand;

  for (const auto& lhs : lhsIter(lit, _ord)) {
    TypedTermList rhs(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort());
    for (const auto& qr : iterTraits(_linearChainSubtermIndex.getUnifications(rhs, /*retrieveSubstitutions=*/true))) {
      if (isReached(cl, rhs, qr.data->term, qr.data->chain, *qr.unifier.ptr(), /*goalIsResult=*/true)) {
        addGoalClause(cl);
        return;
      }
      if (!qr.data->chain->expanded) {
        toExpand.insert(qr.data->chain);
      }
    }
  }

  // insert as non-goal clause
  handleNonGoalClause(cl, /*insert=*/true);
  _nonLinearityHandler.addNonGoalClause(cl);

  for (const auto& chain : iterTraits(toExpand.iter())) {
    ASS(!chain->expanded);
    // amend indices with this RHS of chain
    if (chain->rhs.isNonEmpty()) {
      _chainRHSIndex.handle(TermChain{ chain->rhs, chain }, /*insert=*/true);
    }
    for (auto&& newChain : chainForward(chain)) {
      _newChainsToHandle.push_back(newChain);
    }
    chain->expanded = true;
  }
}

void GoalReachabilityHandler::removeClause(Clause* cl)
{
  if (cl->isGoalClause()) {
    Stack<Chain*> chains;
    ALWAYS(_chainMap.pop(cl, chains));
    // TODO store and remove chains generated by these as well
    for (auto c : chains) {
      handleBaseChain(c, /*insert=*/false);
      handleChain(c, /*expand=*/c->expanded, /*insert=*/false);
      delete c;
    }
  } else {
    handleNonGoalClause(cl, /*insert=*/false);
  }
}

Stack<Chain*> GoalReachabilityHandler::chainForward(Chain* chain)
{
  Stack<Chain*> res;

  // forward: (query) l -> r and (result) s[r'] -> t into lσ -> tσ where σ = mgu(r,r')
  if (chain->rhs.isNonEmpty()) {
    for (const auto& qr : iterTraits(_nonlinearChainSubtermIndex.getUnifications(chain->rhs, /*retrieveSubstitutions=*/true))) {
      res.push(combineChains(chain, qr.data->chain, qr.data->term, *qr.unifier.ptr(), /*leftIsResult=*/false));
    }
  }

  return res;
}

void GoalReachabilityHandler::handleNonGoalClause(Clause* cl, bool insert)
{
  DEBUG("handling non-goal clause ", *cl, ", insert = ", insert);
  auto lit = assertUnitEquality(cl);

  ASS(lit->isPositive());
  ASS(!cl->isGoalClause());

  for (const auto& lhs : lhsIter(lit, _ord)) {
    _nonGoalRHSIndex.handle({ TypedTermList(EqHelper::getOtherEqualitySide(lit, lhs), lhs.sort()), lit, cl }, insert);
  }
  if (!insert) {
    _superposableTerms.remove(cl);
  }
}

void GoalReachabilityHandler::handleBaseChain(Chain* chain, bool insert)
{
  DEBUG("handling base chain ", *chain, ", insert = ", insert);
  ASS(chain->isBase);
  if (chain->lhs.isVar()) {
    return;
  }

  for (const auto& t : iterTraits(NonVariableNonTypeIterator(chain->lhs.term(), /*includeSelf=*/chain->length==0))) {
    _nonlinearChainSubtermIndex.handle(TermChain{ t, chain }, insert);
  }

  _nonLinearityHandler.handleChain(chain, insert);
}

void GoalReachabilityHandler::handleChain(Chain* chain, bool expand, bool insert)
{
  DEBUG("handling chain ", *chain, ", expand = ", expand, ", insert = ", insert);
  // variables do not need to be inserted into the subterm indices
  if (chain->origLhs.isTerm()) {
    ASS(chain->lhs.isTerm());
    ASS(chain->linearLhs.isTerm());

    if (chain->length == 0) {
      _linearChainSubtermIndex.handle(TermChain{ chain->linearLhs.term(), chain }, insert);
    }
    SubtermIterator itO(chain->origLhs.term());
    SubtermIterator itL(chain->linearLhs.term());
    while (itO.hasNext()) {
      ALWAYS(itL.hasNext());
      auto tO = itO.next();
      auto tL = itL.next();
      if (tO.isVar()) {
        itL.right();
        continue;
      }
      if (tL.isVar()) {
        continue;
      }
      _linearChainSubtermIndex.handle(TermChain{ tL.term(), chain }, insert);
    }

    // for (const auto& t : iterTraits(NonVariableNonTypeIterator(chain->linearLhs.term(), /*includeSelf=*/chain->length==0))) {
    //   _linearChainSubtermIndex.handle(TermChain{ t, chain }, insert);
    // }
  }
  // only insert RHS if it is to be expanded
  if (expand) {
    if (chain->rhs.isNonEmpty()) {
      _chainRHSIndex.handle(TermChain{ chain->rhs, chain }, insert);
    }
  }
}

void GoalReachabilityHandler::addSuperposableTerm(Clause* ngcl, Term* t)
{
  DHSet<Term*>* ptr;
  _superposableTerms.getValuePtr(ngcl, ptr);
  if (ptr->insert(t)) {
    _newSuperposableTerms.emplace(ngcl, t);
    DEBUG("could insert ", *t, " for ", *ngcl);
  }
}

// GoalNonLinearityHandler

GoalNonLinearityHandler::GoalNonLinearityHandler(SaturationAlgorithm& salg, GoalReachabilityHandler& handler)
  : ord(salg.getOrdering()),
    handler(handler),
    _lhsIndex(salg.getGeneratingIndex<SuperpositionLHSIndex>()),
    _subtermIndex(salg.getGeneratingIndex<SuperpositionSubtermIndex>()) {}

void GoalNonLinearityHandler::addNonGoalClause(Clause* cl)
{
  DEBUG("linearity addNonGoalClause ", *cl);
  auto lit = assertUnitEquality(cl);
  ASS(!cl->isGoalClause());

  for (auto lhs : lhsIter(lit, ord)) {
    if (lhs.isVar()) {
      continue;
    }
    for (const auto& t : iterTraits(NonVariableNonTypeIterator(lhs.term(), /*includeSelf=*/true))) {
      // handle equality lhs
      if (t == lhs && lit->isPositive()) {
        for (const auto& qr : iterTraits(_nonLinearGoalTermIndex.getUnifications(t, /*retrieveSubstitutions=*/true))) {
          perform(cl, qr.data->term, t, qr.data->chain->constraints, *qr.unifier.ptr(), /*goalIsResult=*/true);
        }
      }
      for (const auto& qr : iterTraits(_nonLinearGoalLHSIndex.getUnifications(t, /*retrieveSubstitutions=*/true))) {
        perform(cl, qr.data->term, t, qr.data->chain->constraints, *qr.unifier.ptr(), /*goalIsResult=*/true);
      }
    }
  }
}

void GoalNonLinearityHandler::handleChain(Chain* chain, bool insert)
{
  DEBUG("linearity handling chain ", *chain, ", insert = ", insert);
  ASS(chain->isBase);
  if (chain->lhs.isVar()) {
    return;
  }

  _nonLinearGoalLHSIndex.handle(TermChain{ chain->linearLhs, chain }, /*insert=*/insert);

  if (insert) {
    for (const auto& qr : iterTraits(_subtermIndex->getUnifications(chain->linearLhs, /*retrieveSubstitutions=*/true))) {
      perform(qr.data->clause, chain->linearLhs, qr.data->term, chain->constraints, *qr.unifier.ptr(), /*goalIsResult=*/false);
    }
  }

  for (const auto& t : iterTraits(NonVariableNonTypeIterator(chain->linearLhs.term(), /*includeSelf=*/true))) {
    _nonLinearGoalTermIndex.handle(TermChain{ t, chain }, /*insert=*/insert);

    if (insert) {
      for (const auto& qr : iterTraits(_lhsIndex->getUnifications(t, /*retrieveSubstitutions=*/true))) {
        perform(qr.data->clause, t, qr.data->term, chain->constraints, *qr.unifier.ptr(), /*goalIsResult=*/false);
      }
    }
  }
}

ClauseTermPairs GoalNonLinearityHandler::get(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm, const LinearityConstraints& cons, ResultSubstitution& subst, bool goalIsResult)
{
  ASS(!ngcl->isGoalClause());
  if (cons.isEmpty() || nonGoalTerm.isVar()) {
    return ClauseTermPairs();
  }
  ASS(goalTerm.isTerm());

  DEBUG("linearity unifying ", goalTerm.untyped(), " with ", nonGoalTerm.untyped(), " with constraints ", cons);

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

  auto tl = List<TermList>::empty();
  bool unifies = true;

  for (const auto& [x,y] : cons) {
    ASS(x.isVar());
    ASS(y.isVar());
    if (unifies && !subst.constrain(x, y, goalIsResult)) {
      unifies = false;
    }
    auto xptr = map.findPtr(x.var());
    if (xptr && xptr->isTerm()) {
      List<TermList>::push(*xptr, tl);
    }
    auto yptr = map.findPtr(y.var());
    if (yptr && yptr->isTerm()) {
      List<TermList>::push(*yptr, tl);
    }
  }

  ClauseTermPairs res;
  if (!unifies) {
    ord.removeNonMaximal(tl);
    DEBUG("linearity cannot not unify");
    while (tl) {
      auto t = List<TermList>::pop(tl);
      DEBUG("linearity adding ", t, " for ", *ngcl);
      res.emplace(ngcl, t.term());
    }
  }
  return res;
}

void GoalNonLinearityHandler::perform(Clause* ngcl, TypedTermList goalTerm, TypedTermList nonGoalTerm, const LinearityConstraints& cons, ResultSubstitution& subst, bool goalIsResult)
{
  // TODO maybe put this somewhere else
  if (ngcl->isGoalClause()) {
    return;
  }
  ASS(goalTerm.isTerm());
  ASS(nonGoalTerm.isTerm());

  for (auto [cl, t] : get(ngcl, goalTerm, nonGoalTerm, cons, subst, goalIsResult)) {
    handler.addSuperposableTerm(ngcl, t);
  }
}
