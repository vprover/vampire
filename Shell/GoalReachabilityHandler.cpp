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
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Lib/Exception.hpp"

using namespace Shell;
using namespace Kernel;

#define DEBUG(...) // DBG(__VA_ARGS__)

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

TypedTermList typedLit(Term* lit)
{ return TypedTermList(TermList(lit), AtomicSort::boolSort()); }

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
    auto res = linearizer.transform(lhs.term());
    if (res->isLiteral()) {
      linearLhs = typedLit(res);
    } else {
      linearLhs = res;
    }
    constraints = linearizer.constraints;
  }

  // env.statistics->numberOfChains++;
  // if (length > env.statistics->maxChainLength) {
  //   env.statistics->maxChainLength = length;
  // }
}

void GoalReachabilityHandler::handleGoalClause(Clause* cl, bool adding)
{
  DEBUG("handleGoalClause ", adding, " ", *cl);
  
  for (const auto lit : cl->getSelectedLiteralIterator()) {
    ASS(lit->isEquality());

    for (const auto& tt : iterTraits(EqHelper::getSubtermIterator</*higherOrder=*/false>(lit, _ord))) {
      // TODO: linearize
      if (lit->isPositive()) {
        _chain1ForwardIndex.handle(TermLiteralClause{ tt, lit, cl }, /*insert=*/true);
      } else {
        _baseForwardIndex.handle(TermLiteralClause{ tt, lit, cl }, /*insert=*/true);
      }
    }

    for (const auto& lhs : iterTraits(EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt))) {
	    _chain2ForwardIndex.handle(TermLiteralClause{ lhs, lit, cl }, /*insert=*/true);
    }
  }

  _newGoalClauses.push(cl);
}

bool GoalReachabilityHandler::iterate()
{
  DEBUG("iterate");

  unsigned cnt = 0;

  while (_todo.isNonEmpty()) {

    if (cnt++ >= _chainLimit) {
      return false;
    }

    auto [cl,t] = _todo.pop_front();

    // if we find a forward base inference with t, we are done
    if (_baseForwardIndex.getUnifications(t, false).hasNext()) {
      updateWatchedLiteral(cl);
      continue;
    }

    // TODO add to backward index
    handleNonGoalTerm(cl, t);

    if (t.isVar()) {
      ASS(!_chain1ForwardIndex.getUnifications(t, /*retrieveSubstitutions=*/true).hasNext());
      continue;
    }

    // forward chain_1 inferences
    for (const auto& qr : iterTraits(_chain1ForwardIndex.getUnifications(t, /*retrieveSubstitutions=*/true))) {
      auto term = qr.data->term;
      auto lit = qr.data->literal;
      auto [lhs, rhs] = lit->eqArgs();
      auto sortS = qr.unifier->applyToResult(lit->eqArgSort());
      auto lhsS = qr.unifier->applyToResult(lhs);
      auto rhsS = qr.unifier->applyToResult(rhs);
      auto comp = _ord.compare(lhsS, rhsS);

      if (lhs.containsSubterm(term) && !Ordering::isGreaterOrEqual(Ordering::reverse(comp))) {
        _todo.push_back(std::make_pair(cl, TypedTermList(rhsS, sortS)));
      }
      if (rhs.containsSubterm(term) && !Ordering::isGreaterOrEqual(comp)) {
        _todo.push_back(std::make_pair(cl, TypedTermList(lhsS, sortS)));
      }
    }

    // forward chain_2 inferences (chain_1 and chain_2 coincide on the term itself, so we skip that)
    for (const auto& st : iterTraits(NonVariableNonTypeIterator(t.term(), /*includeSelf=*/false))) {
      for (const auto& qr : iterTraits(_chain2ForwardIndex.getUnifications(st, /*retrieveSubstitutions=*/true))) {
        auto lhs = qr.data->term;
        auto lit = qr.data->literal;
        auto rhs = EqHelper::getOtherEqualitySide(lit, lhs);
        auto lhsS = qr.unifier->applyToResult(lhs);
        auto rhsS = qr.unifier->applyToResult(rhs);

        if (Ordering::isGreaterOrEqual(_ord.compare(rhsS, lhsS))) {
          continue;
        }

        _todo.push_back(std::make_pair(cl,
          EqHelper::replace(qr.unifier->applyToQuery(t).term(), lhsS, rhsS)));
      }
    }
  }

  return true;
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

  for (unsigned i = 0; i < cl->size(); i++) {
    auto lit = (*cl)[i];
    if (lit->isNegative()) {
      continue;
    }

    // this literal will be watched, add its sides to the TODO deque
    auto [lhs,rhs] = lit->eqArgs();
    auto sort = lit->eqArgSort();
    _todo.push_back(std::make_pair(cl, TypedTermList(lhs, sort)));
    _todo.push_back(std::make_pair(cl, TypedTermList(rhs, sort)));

    // TODO save info s.t. we can remove this clause later
    _nonGoalWatchedLiterals.insert(cl, i);
    return;
  }

  // otherwise clause is goal clause, add it
  handleGoalClause(cl, /*adding=*/true);
}

void GoalReachabilityHandler::updateWatchedLiteral(Clause* cl)
{
  DEBUG("updateWatchedLiteral ", *cl);

  auto ptr = _nonGoalWatchedLiterals.findPtr(cl);

  // TODO remove previous watched literal from indices

  for (; *ptr < cl->size(); (*ptr)++) {
    auto lit = (*cl)[*ptr];
    if (lit->isNegative()) {
      continue;
    }

    // this literal will be watched, add its sides to the TODO deque
    auto [lhs,rhs] = lit->eqArgs();
    auto sort = lit->eqArgSort();
    _todo.push_back(std::make_pair(cl, TypedTermList(lhs, sort)));
    _todo.push_back(std::make_pair(cl, TypedTermList(rhs, sort)));
    return;
  }

  // otherwise clause is goal clause, add it
  handleGoalClause(cl, /*adding=*/true);
}

void GoalReachabilityHandler::removeClause(Clause* cl)
{
  INVALID_OPERATION("not yet implemented");
//   // if (cl->isGoalClause()) {
//     Stack<Chain*> chains;
//     ALWAYS(_chainMap.pop(cl, chains));
//     // TODO store and remove chains generated by these as well
//     for (auto c : chains) {
//       handleBaseChain(c, /*insert=*/false);
//       if (c->processed) {
//         handleChain(c, /*expand=*/c->expanded, /*insert=*/false);
//       } else {
//         // remove chain from unprocessed queue
//         // TODO make this more efficient
//         int index = -1;
//         for (unsigned i = 0; i < _newChainsToHandle.size(); i++) {
//           if (_newChainsToHandle[i] == c) {
//             _newChainsToHandle[i] = nullptr;
//             index = i;
//             break;
//           }
//         }
//         ASS_NEQ(index, -1);
// #if VDEBUG
//         for (unsigned i = index + 1; i < _newChainsToHandle.size(); i++) {
//           ASS_NEQ(_newChainsToHandle[i], c);
//         }
// #endif
//       }
//       delete c;
//     }
//   //   cl->unmakeGoalClause();

//   // } else {
//   //   handleNonGoalClause(cl, /*insert=*/false);
//   // }
}
