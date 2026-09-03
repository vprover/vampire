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
#include "Kernel/EqHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Lib/Exception.hpp"

using namespace Shell;
using namespace Kernel;

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace {
  struct Linearizer : TermTransformer {
    Linearizer(unsigned freshVar) : TermTransformer(false), freshVar(freshVar) {}
    TermList transformSubterm(TermList trm) override {
      if (trm.isVar() && !seen.insert(trm.var())) {
        return TermList::var(freshVar++);
      }
      return trm;
    }
    DHSet<unsigned> seen;
    unsigned freshVar;
  };
}

TypedTermList linearize(TypedTermList t, unsigned freshVar) {
  if (t.isVar()) {
    return t;
  }
  Linearizer linearizer(freshVar);
  return TypedTermList(linearizer.transform(t.term()));
}

void GoalReachabilityHandler::handleGoalClause(Clause* cl, bool adding)
{
  DEBUG("handleGoalClause ", adding, " ", *cl);

  ASS(cl->numSelected());

  auto freshVar = cl->maxVar() + 1;

  DHSet<Clause*> needsUpdating;

  for (const auto lit : cl->getSelectedLiteralIterator()) {
    ASS(lit->isEquality());

    for (const TypedTermList& tt : iterTraits(EqHelper::getSubtermIterator</*higherOrder=*/false>(lit, _ord))) {
      auto ttl = linearize(tt,freshVar);
      if (lit->isPositive()) {
        _chain1ForwardIndex.handle(TermWithValue{ ttl, TermLiteralClause{ tt, lit, cl } }, adding);
        if (adding) {
          // backward base_2 inferences
          for (const auto& qr : iterTraits(_backwardTermIndex.getUnifications(ttl, /*retrieveSubstitutions=*/true))) {
            if (base2Inference(qr.data->value, tt, lit, *qr.unifier, /*tIsResult=*/false)) {
              needsUpdating.insert(qr.data->value);
            }
          }
          // backward chain_1 inferences
          for (const auto& qr : iterTraits(_backwardTermIndex.getUnifications(ttl, /*retrieveSubstitutions=*/true))) {
            chain1Inference(qr.data->value, tt, lit, *qr.unifier, /*tIsResult=*/false);
          }
        }
      } else {
        _baseForwardIndex.handle(TermWithValue{ ttl, TermLiteralClause{ tt, lit, cl } }, adding);
        if (adding) {
          for (const auto& qr : iterTraits(_backwardTermIndex.getUnifications(ttl, /*retrieveSubstitutions=*/false))) {
            if (baseInference(qr.data->value, tt, lit, *qr.unifier, /*tIsResult=*/false)) {
              needsUpdating.insert(qr.data->value);
            }
          }
        }
      }
    }

    for (const auto& lhs : iterTraits(EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt))) {
      auto lhsl = linearize(lhs, freshVar);
	    _chain2ForwardIndex.handle(TermWithValue{ lhsl, TermLiteralClause{ lhs, lit, cl } }, adding);
      if (adding) {
        for (const auto& qr : iterTraits(_backwardSubtermIndex.getUnifications(lhsl, /*retrieveSubstitutions=*/true))) {
          chain2Inference(qr.data->value.second, qr.data->value.first, lhs, lit, *qr.unifier, /*lhsIsResult=*/false);
        }
      }
    }
  }

  for (const auto& ncl : iterTraits(needsUpdating.iter())) {
    updateWatchedLiteral(ncl);
  }

  _newGoalClauses.push(cl);
}

void GoalReachabilityHandler::handleNonGoalTerm(Clause* cl, TypedTermList t, bool adding)
{
  _backwardTermIndex.handle({ t, cl }, adding);
  if (t.isTerm()) {
    for (const auto& st : iterTraits(NonVariableNonTypeIterator(t.term(), /*includeSelf=*/false))) {
      _backwardSubtermIndex.handle({ st, { t, cl } }, adding);
    }
  }
}

bool GoalReachabilityHandler::iterate()
{
  DEBUG("iterate");

  unsigned cnt = 0;

  while (_todoGoalClauses.isNonEmpty()) {

    if (cnt++ >= _chainLimit) {
      return false;
    }

    auto curr = _todoGoalClauses.pop_front();
    DEBUG("processing goal clause ", *curr);
    handleGoalClause(curr, /*adding=*/true);
  }

  while (_todoNonGoalClauses.isNonEmpty()) {

    if (cnt++ >= _chainLimit) {
      return false;
    }

    auto cl = _todoNonGoalClauses.pop_front();
    auto ptr = _nonGoalClauses.findPtr(cl);
    if (!ptr) {
      continue;
    }
    if (ptr->unprocessed.isEmpty()) {
      // clause will be added to todo again via backward inferences if needed
      continue;
    }
    DEBUG("processing non-goal clause ", *cl);
    auto t = ptr->unprocessed.pop();
    DEBUG("processing term ", t);
    if (!ptr->seen.insert(t)) {
      DEBUG("already seen");
      continue;
    }

    // if we find a forward base inference with t, we are done for this term
    if (iterTraits(_baseForwardIndex.getUnifications(t, /*retrieveSubstitutions=*/true)).any([this,cl](const auto& qr) {
      return baseInference(cl, qr.data->value.term, qr.data->value.literal, *qr.unifier, /*tIsResult=*/true);
    })) {
      updateWatchedLiteral(cl);
      continue;
    }

    // if we find a forward base_2 inference with t, we are done for this term
    if (iterTraits(_chain1ForwardIndex.getUnifications(t, /*retrieveSubstitutions=*/true)).any([this,cl](const auto& qr) {
      return base2Inference(cl, qr.data->value.term, qr.data->value.literal, *qr.unifier, /*tIsResult=*/true);
    })) {
      updateWatchedLiteral(cl);
      continue;
    }

    ptr->processed.push(t);
    handleNonGoalTerm(cl, t, /*adding=*/true);

    if (t.isVar()) {
      ASS(!_chain1ForwardIndex.getUnifications(t, /*retrieveSubstitutions=*/true).hasNext());
      _todoNonGoalClauses.push_back(cl);
      continue;
    }

    // forward chain_1 inferences
    for (const auto& qr : iterTraits(_chain1ForwardIndex.getUnifications(t, /*retrieveSubstitutions=*/true))) {
      chain1Inference(cl, qr.data->value.term, qr.data->value.literal, *qr.unifier, /*tIsResult=*/true);
    }

    // forward chain_2 inferences (chain_1 and chain_2 coincide on the term itself, so we skip that)
    for (const auto& st : iterTraits(NonVariableNonTypeIterator(t.term(), /*includeSelf=*/false))) {
      for (const auto& qr : iterTraits(_chain2ForwardIndex.getUnifications(st, /*retrieveSubstitutions=*/true))) {
        chain2Inference(cl, t, qr.data->value.term, qr.data->value.literal, *qr.unifier, /*lhsIsResult=*/true);
      }
    }
    _todoNonGoalClauses.push_back(cl);
  }

  return _todoGoalClauses.isEmpty();
}

GoalReachabilityHandler::GoalReachabilityHandler(SaturationAlgorithm& salg)
  : _ord(salg.getOrdering()),
    _opt(salg.getOptions()),
    _chainLimit(salg.getOptions().goalOrientedChainLimit())
{
  if (salg.getProblem().hasPolymorphicSym()) {
    INVALID_OPERATION("polymorphism is not yet handled");
  }
  if (salg.getProblem().isHigherOrder()) {
    INVALID_OPERATION("HOL is not yet handled");
  }
}

void GoalReachabilityHandler::addClause(Clause* cl)
{
  DEBUG("addClause ", *cl);

  ASS(cl->numSelected());

  for (unsigned i = 0; i < cl->size(); i++) {
    auto lit = (*cl)[i];
    if (lit->isNegative()) {
      continue;
    }

    // this literal will be watched, add its sides to the TODO deque
    auto [lhs,rhs] = lit->eqArgs();
    auto sort = lit->eqArgSort();

    NonGoalClauseInfo info;
    info.unprocessed.emplace(lhs, sort);
    info.unprocessed.emplace(rhs, sort);
    info.watchedIndex = i;
    _todoNonGoalClauses.push_back(cl);
    _nonGoalClauses.insert(cl, std::move(info));
    return;
  }

  _todoGoalClauses.push_back(cl);
}

bool GoalReachabilityHandler::updateWatchedLiteral(Clause* cl)
{
  DEBUG("updateWatchedLiteral ", *cl);

  auto ptr = _nonGoalClauses.findPtr(cl);

  ASS(ptr);
  (ptr->watchedIndex)++;

  for (; ptr->watchedIndex < cl->size(); (ptr->watchedIndex)++) {
    auto lit = (*cl)[ptr->watchedIndex];
    if (lit->isNegative()) {
      continue;
    }

    // this literal will be watched, add its sides to the TODO deque
    auto [lhs,rhs] = lit->eqArgs();
    auto sort = lit->eqArgSort();
    // remove indexed terms
    while (ptr->processed.isNonEmpty()) {
      handleNonGoalTerm(cl, ptr->processed.pop(), /*adding=*/false);
    }
    if (ptr->unprocessed.isEmpty()) {
      _todoNonGoalClauses.push_back(cl);
    } else {
      ptr->unprocessed.reset();
    }
    ptr->unprocessed.emplace(lhs, sort);
    ptr->unprocessed.emplace(rhs, sort);
    return false;
  }

  // remove indexed terms
  while (ptr->processed.isNonEmpty()) {
    handleNonGoalTerm(cl, ptr->processed.pop(), /*adding=*/false);
  }
  _nonGoalClauses.remove(cl);
  _todoGoalClauses.push_back(cl);
  return true;
}

bool GoalReachabilityHandler::baseInference(Clause* cl, TermList t, Literal* lit, ResultSubstitution& unif, bool tIsResult)
{
  DEBUG("base inference ", t, " ", *lit, " ", *cl);

  auto [lhs, rhs] = lit->eqArgs();
  auto lhsS = unif.applyTo(lhs, tIsResult);
  auto rhsS = unif.applyTo(rhs, tIsResult);
  auto comp = _ord.compare(lhsS, rhsS);

  if (lhs.containsSubterm(t) && !Ordering::isGreaterOrEqual(Ordering::reverse(comp))) {
    return true;
  }
  if (rhs.containsSubterm(t) && !Ordering::isGreaterOrEqual(comp)) {
    return true;
  }
  return false;
}

bool GoalReachabilityHandler::base2Inference(Clause* cl, TermList t, Literal* lit, ResultSubstitution& unif, bool tIsResult)
{
  DEBUG("base_2 inference ", t, " ", *lit, " ", *cl);

  auto [lhs, rhs] = lit->eqArgs();
  auto sortS = unif.applyTo(lit->eqArgSort(), tIsResult);
  auto lhsS = unif.applyTo(lhs, tIsResult);
  auto rhsS = unif.applyTo(rhs, tIsResult);
  auto comp = _ord.compare(lhsS, rhsS);

  if (lhs.containsSubterm(t) && !Ordering::isGreaterOrEqual(Ordering::reverse(comp))) {
    if (iterTraits(_baseForwardIndex.getUnifications(TypedTermList(lhsS, sortS), /*retrieveSubstitutions=*/true)).any([this,cl](const auto& qr) {
      return baseInference(cl, qr.data->value.term, qr.data->value.literal, *qr.unifier, /*tIsResult=*/true);
    })) {
      return true;
    }
  }
  if (rhs.containsSubterm(t) && !Ordering::isGreaterOrEqual(comp)) {
    if (iterTraits(_baseForwardIndex.getUnifications(TypedTermList(rhsS, sortS), /*retrieveSubstitutions=*/true)).any([this,cl](const auto& qr) {
      return baseInference(cl, qr.data->value.term, qr.data->value.literal, *qr.unifier, /*tIsResult=*/true);
    })) {
      return true;
    }
  }
  return false;
}

void GoalReachabilityHandler::chain1Inference(Clause* cl, TermList t, Literal* lit, ResultSubstitution& unif, bool tIsResult)
{
  DEBUG("chain_1 inference ", t, " ", *lit, " ", *cl);

  auto [lhs, rhs] = lit->eqArgs();
  auto sortS = unif.applyTo(lit->eqArgSort(), tIsResult);
  auto lhsS = unif.applyTo(lhs, tIsResult);
  auto rhsS = unif.applyTo(rhs, tIsResult);
  auto comp = _ord.compare(lhsS, rhsS);

  auto ptr = _nonGoalClauses.findPtr(cl);
  ASS(ptr);
  if (lhs.containsSubterm(t) && !Ordering::isGreaterOrEqual(Ordering::reverse(comp))) {
    if (ptr->unprocessed.isEmpty()) {
      _todoNonGoalClauses.push_back(cl);
    }
    ptr->unprocessed.emplace(lhsS, sortS); // TODO: adding the lhs like this is not very efficient
    ptr->unprocessed.emplace(rhsS, sortS);
  }
  if (rhs.containsSubterm(t) && !Ordering::isGreaterOrEqual(comp)) {
    if (ptr->unprocessed.isEmpty()) {
      _todoNonGoalClauses.push_back(cl);
    }
    ptr->unprocessed.emplace(rhsS, sortS); // TODO: adding the rhs like this is not very efficient
    ptr->unprocessed.emplace(lhsS, sortS);
  }
}

void GoalReachabilityHandler::chain2Inference(Clause* cl, TermList t, TermList lhs, Literal* lit, ResultSubstitution& unif, bool lhsIsResult)
{
  DEBUG("chain_2 inference ", t, " ", lhs, " ", *lit, " ", *cl);

  auto rhs = EqHelper::getOtherEqualitySide(lit, lhs);
  auto lhsS = unif.applyTo(lhs, lhsIsResult);
  auto rhsS = unif.applyTo(rhs, lhsIsResult);

  if (Ordering::isGreaterOrEqual(_ord.compare(rhsS, lhsS))) {
    return;
  }

  auto ptr = _nonGoalClauses.findPtr(cl);
  ASS(ptr);
  if (ptr->unprocessed.isEmpty()) {
    _todoNonGoalClauses.push_back(cl);
  }
  ptr->unprocessed.emplace(EqHelper::replace(unif.applyTo(t, !lhsIsResult).term(), lhsS, rhsS));
}

void GoalReachabilityHandler::removeClause(Clause* cl)
{
  INVALID_OPERATION("not yet implemented");
}
