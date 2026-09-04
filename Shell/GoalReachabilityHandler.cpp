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
#include "Inferences/DemodulationHelper.hpp"
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

Literal* linearize(Literal* lit, unsigned freshVar) {
  Linearizer linearizer(freshVar);
  return linearizer.transformLiteral(lit);
}

void GoalReachabilityHandler::handleGoalClause(Clause* cl, bool adding)
{
  DEBUG("handleGoalClause ", adding, " ", cl->toString());

  ASS(cl->numSelected());

  auto freshVar = cl->maxVar() + 1;

  DHSet<Clause*> needsUpdating;

  for (const auto lit : cl->getSelectedLiteralIterator()) {

    for (const TypedTermList& tt : iterTraits(EqHelper::getSubtermIterator</*higherOrder=*/false>(lit, _ord))) {
      auto ttl = linearize(tt,freshVar);
      if (lit->isPositive()) {
        _chain1ForwardIndex.handle(TermWithValue{ ttl, TermLiteralClause{ tt, lit, cl } }, adding);
        if (adding) {
          // backward base_2 inferences
          for (const auto& qr : iterTraits(_backwardTermIndex.getUnifications(ttl, /*retrieveSubstitutions=*/true))) {
            if (base2Inference(qr.data->value, tt, *qr.unifier, /*tIsResult=*/false)) {
              needsUpdating.insert(qr.data->value);
            }
          }
          // backward chain_1 inferences
          for (const auto& qr : iterTraits(_backwardTermIndex.getUnifications(ttl, /*retrieveSubstitutions=*/true))) {
            chain1Inference(qr.data->value, lit, *qr.unifier, /*tIsResult=*/false);
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

    // I think chain_2 inferences are not needed for literal right premises.
    if (lit->isEquality()) {
      for (const auto& lhs : iterTraits(EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt))) {
        auto lhsl = linearize(lhs, freshVar);
        _chain2ForwardIndex.handle(TermWithValue{ lhsl, TermLiteralClause{ lhs, lit, cl } }, adding);
        if (adding) {
          for (const auto& qr : iterTraits(_backwardSubtermIndex.getUnifications(lhsl, /*retrieveSubstitutions=*/true))) {
            chain2Inference(qr.data->value.second, qr.data->value.first, lhs, lit, *qr.unifier, /*lhsIsResult=*/false);
          }
        }
      }
    } else if (lit->isNegative()) {
      auto litc = Literal::complementaryLiteral(lit);
      auto litl = linearize(litc,freshVar);
      _baseForwardLiteralIndex.handle(LiteralWithValue{ litl, LiteralClause{ litc, cl } }, adding);
      if (adding) {
        for (const auto& qr : iterTraits(_backwardLiteralIndex.getUnifications(litl, /*complementary=*/false, /*retrieveSubstitutions=*/false))) {
          needsUpdating.insert(qr.data->value);
        }
      }
    }
  }

  ASS(adding || needsUpdating.isEmpty());
  for (const auto& ncl : iterTraits(needsUpdating.iter())) {
    updateWatchedLiteral(ncl);
  }
}

void GoalReachabilityHandler::handleNonGoalTerm(Clause* cl, TypedTermList t, bool adding)
{
  if (t.term()->isLiteral()) {
    _backwardLiteralIndex.handle({ static_cast<Literal*>(t.term()), cl }, adding);
    return;
  }
  _backwardTermIndex.handle({ t, cl }, adding);
  if (t.isTerm()) {
    for (const auto& st : iterTraits(NonVariableNonTypeIterator(t.term(), /*includeSelf=*/false))) {
      _backwardSubtermIndex.handle({ st, { t, cl } }, adding);
    }
  }
}

bool GoalReachabilityHandler::iterate(ClauseStack& newGoalClauses)
{
  DEBUG("iterate");

  unsigned cnt = 0;

  while (!_todoGoalClauses.empty()) {

    if (cnt++ >= _chainLimit) {
      return false;
    }

    auto curr = _todoGoalClauses.front();
    _todoGoalClauses.pop_front();
    DEBUG("processing goal clause ", curr->toString());
    handleGoalClause(curr, /*adding=*/true);
    newGoalClauses.push(curr);
  }

  while (!_todoNonGoalClauses.empty()) {

    if (cnt++ >= _chainLimit) {
      return false;
    }

    auto cl = _todoNonGoalClauses.front();
    _todoNonGoalClauses.pop_front();
    auto ptr = _nonGoalClauses.findPtr(cl);
    if (!ptr) {
      // clause was removed in between from the todo list
      continue;
    }
    if (ptr->unprocessed.empty()) {
      // clause will be added to todo again via backward inferences if needed
      continue;
    }
    DEBUG("processing non-goal clause ", cl->toString());
    auto t = ptr->unprocessed.front();
    ptr->unprocessed.pop_front();
    DEBUG("processing term ", t);
    if (!ptr->seen.insert(t)) {
      DEBUG("already seen");
      _todoNonGoalClauses.push_back(cl);
      continue;
    }

    if (t.term()->isLiteral()) {

      auto lit = static_cast<Literal*>(t.term());
      ASS(lit->isPositive());
      ASS(!lit->isEquality());

      // if we find a forward base inference with lit, we are done for this term
      if (iterTraits(_baseForwardLiteralIndex.getUnifications(lit, /*complementary=*/false, /*retrieveSubstitutions=*/true)).hasNext()) {
        updateWatchedLiteral(cl);
        continue;
      }

    } else {
      // if we find a forward base inference with t, we are done for this term
      if (iterTraits(_baseForwardIndex.getUnifications(t, /*retrieveSubstitutions=*/true)).any([this,cl](const auto& qr) {
        return baseInference(cl, qr.data->value.term, qr.data->value.literal, *qr.unifier, /*tIsResult=*/true);
      })) {
        updateWatchedLiteral(cl);
        continue;
      }

      // if we find a forward base_2 inference with t, we are done for this term
      if (iterTraits(_chain1ForwardIndex.getUnifications(t, /*retrieveSubstitutions=*/true)).any([this,cl](const auto& qr) {
        return base2Inference(cl, qr.data->value.term, *qr.unifier, /*tIsResult=*/true);
      })) {
        updateWatchedLiteral(cl);
        continue;
      }
    }

    ptr->processed.push(t);
    handleNonGoalTerm(cl, t, /*adding=*/true);

    if (t.isVar()) {
      // for variables, it suffices to check base inferences, if there is no base term that
      // unifies with them (i.e. has unifying sort), then there shouldn't be any unifying chain either.
      ASS(!_chain1ForwardIndex.getUnifications(t, /*retrieveSubstitutions=*/true).hasNext());
      _todoNonGoalClauses.push_back(cl);
      continue;
    }

    // I think chain_1 inferences are not needed for literal left premises, as (implicit)
    // right hand sides are never used and the rest is covered by base inferences.
    if (!t.term()->isLiteral()) {
      // forward chain_1 inferences
      for (const auto& qr : iterTraits(_chain1ForwardIndex.getUnifications(t, /*retrieveSubstitutions=*/true))) {
        chain1Inference(cl, qr.data->value.literal, *qr.unifier, /*tIsResult=*/true);
      }
    }

    // forward chain_2 inferences (chain_1 and chain_2 coincide on the term itself, so we skip that)
    for (const auto& st : iterTraits(NonVariableNonTypeIterator(t.term(), /*includeSelf=*/false))) {
      for (const auto& qr : iterTraits(_chain2ForwardIndex.getUnifications(st, /*retrieveSubstitutions=*/true))) {
        chain2Inference(cl, t, qr.data->value.term, qr.data->value.literal, *qr.unifier, /*lhsIsResult=*/true);
      }
    }
    _todoNonGoalClauses.push_back(cl);
  }

  return _todoGoalClauses.empty();
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
  DEBUG("addClause ", cl->toString());

  ASS(cl->numSelected());

  for (unsigned i = 0; i < cl->size(); i++) {
    auto lit = (*cl)[i];
    if (lit->isNegative()) {
      continue;
    }

    NonGoalClauseInfo info;
    if (lit->isEquality()) {
      auto [lhs,rhs] = lit->eqArgs();
      auto sort = lit->eqArgSort();
      info.unprocessed.emplace_back(lhs, sort);
      info.unprocessed.emplace_back(rhs, sort);
    } else {
      info.unprocessed.emplace_back(lit);
    }
    info.watchedIndex = i;
    _todoNonGoalClauses.push_back(cl);
    _nonGoalClauses.insert(cl, std::move(info));
    return;
  }

  _todoGoalClauses.push_back(cl);
}

void GoalReachabilityHandler::updateWatchedLiteral(Clause* cl)
{
  DEBUG("updateWatchedLiteral ", cl->toString());

  auto ptr = _nonGoalClauses.findPtr(cl);

  ASS(ptr);
  ptr->seen.reset();
  (ptr->watchedIndex)++;

  for (; ptr->watchedIndex < cl->size(); (ptr->watchedIndex)++) {
    auto lit = (*cl)[ptr->watchedIndex];
    if (lit->isNegative()) {
      continue;
    }

    // remove indexed terms
    while (ptr->processed.isNonEmpty()) {
      handleNonGoalTerm(cl, ptr->processed.pop(), /*adding=*/false);
    }
    if (ptr->unprocessed.empty()) {
      _todoNonGoalClauses.push_back(cl);
    } else {
      ptr->unprocessed.clear();
    }
    if (lit->isEquality()) {
      auto [lhs,rhs] = lit->eqArgs();
      auto sort = lit->eqArgSort();
      ptr->unprocessed.emplace_back(lhs, sort);
      ptr->unprocessed.emplace_back(rhs, sort);
    } else {
      ptr->unprocessed.emplace_back(lit);
    }
  }

  // remove indexed terms
  while (ptr->processed.isNonEmpty()) {
    handleNonGoalTerm(cl, ptr->processed.pop(), /*adding=*/false);
  }
  _nonGoalClauses.remove(cl);
  _todoGoalClauses.push_back(cl);
}

bool GoalReachabilityHandler::baseInference(Clause* cl, TermList t, Literal* lit, ResultSubstitution& unif, bool tIsResult)
{
  DEBUG("base inference ", t, " ", *lit, " ", cl->toString());

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

template<typename Object>
bool GoalReachabilityHandler::base2Inference(Clause* cl, Object obj, ResultSubstitution& unif, bool tIsResult)
{
  DEBUG("base_2 inference ", obj, " ", cl->toString());
  struct Appl : SubstApplicator {
    Appl(ResultSubstitution& subst, bool result) : subst(subst), result(result) {}
    TermList apply(unsigned v) const override {
      return subst.apply(TermList::var(v), result);
    }
    ResultSubstitution& subst;
    bool result;
  } appl { unif, tIsResult };
  return DemodulationHelper::isRenamingOn(&appl, obj);
}

void GoalReachabilityHandler::chain1Inference(Clause* cl, Literal* lit, ResultSubstitution& unif, bool tIsResult)
{
  DEBUG("chain_1 inference ", t, " ", *lit, " ", cl->toString());

  auto ptr = _nonGoalClauses.findPtr(cl);
  ASS(ptr);
  if (ptr->unprocessed.empty()) {
    _todoNonGoalClauses.push_back(cl);
  }

  if (lit->isEquality()) {
    auto [lhs, rhs] = lit->eqArgs();
    auto sortS = unif.applyTo(lit->eqArgSort(), tIsResult);
    auto lhsS = unif.applyTo(lhs, tIsResult);
    auto rhsS = unif.applyTo(rhs, tIsResult);
    ptr->unprocessed.emplace_back(lhsS, sortS); // TODO: adding the lhs like this is not very efficient
    ptr->unprocessed.emplace_back(rhsS, sortS);
  } else {
    ptr->unprocessed.emplace_back(unif.applyTo(lit, tIsResult));
  }
}

void GoalReachabilityHandler::chain2Inference(Clause* cl, TermList t, TermList lhs, Literal* lit, ResultSubstitution& unif, bool lhsIsResult)
{
  DEBUG("chain_2 inference ", t, " ", lhs, " ", *lit, " ", cl->toString());

  auto rhs = EqHelper::getOtherEqualitySide(lit, lhs);
  auto lhsS = unif.applyTo(lhs, lhsIsResult);
  auto rhsS = unif.applyTo(rhs, lhsIsResult);

  if (Ordering::isGreaterOrEqual(_ord.compare(rhsS, lhsS))) {
    return;
  }

  auto ptr = _nonGoalClauses.findPtr(cl);
  ASS(ptr);
  if (ptr->unprocessed.empty()) {
    _todoNonGoalClauses.push_back(cl);
  }
  ptr->unprocessed.emplace_back(EqHelper::replace(unif.applyTo(t, !lhsIsResult).term(), lhsS, rhsS));
}

void GoalReachabilityHandler::removeClause(Clause* cl)
{
  ASS_EQ(cl->store(), Clause::SUSPENDED);
  auto ptr = _nonGoalClauses.findPtr(cl);
  if (!ptr) {
    auto num_removed = std::erase(_todoGoalClauses, cl);
    ASS_LE(num_removed, 1);
    if (!num_removed) {
      handleGoalClause(cl, /*adding=*/false);
    }
    return;
  }

  // remove indexed terms
  while (ptr->processed.isNonEmpty()) {
    handleNonGoalTerm(cl, ptr->processed.pop(), /*adding=*/false);
  }
  _nonGoalClauses.remove(cl);
  std::erase(_todoNonGoalClauses, cl);
}
