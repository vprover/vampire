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
 * @file Unifier.cpp
 * Implements class Unifier.
 */

#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"

#include "Unifier.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace HOL {

// Unifier

Unifier::Unifier(Literal* lit, Literal* def, unsigned nextVar)
  : _lit(lit), _todo({ new Node(lit, def, nextVar )}) {}

bool Unifier::iterate(LiteralStack& solution)
{
  ASS(solution.isEmpty());

  if (_todo.isEmpty()) {
    return true; // finished
  }

  auto curr = _todo.pop();
  DEBUG("curr ", *curr);

  auto [children, sol] = curr->solve();
  ASS(children.isEmpty() || sol.isEmpty());

  if (sol.isNonEmpty()) {
    solution = std::move(sol);
  }
  for (const auto& child : children) {
    _todo.push(child);
  }
  return _todo.isEmpty();
}

// Constraint

struct Unifier::Constraint
{
  TermList _lhs;
  TermList _rhs;
  TermList _sort;
  TermList _lhead;
  TermList _rhead;

  Constraint(TermList lhs, TermList rhs, TermList sort)
    : _lhs(lhs), _rhs(rhs), _sort(sort), _lhead(lhs.head()), _rhead(rhs.head())
  {
    // terms must be in whnf
    ASS(!_lhead.isLambdaTerm());
    ASS(!_lhead.isLambdaTerm());
  }

  bool flexFlex()   const { return _lhead.isVar() && _rhead.isVar(); }
  bool rigidRigid() const { return _lhead.isTerm() && _rhead.isTerm(); }
  bool flexRigid()  const { return !flexFlex() && !rigidRigid(); }

  bool derefHead(TermList& head, TermList& side, const Substitution& subs)
  {
    if (head.isVar()) {
      TermList t;
      if (subs.findBinding(head.var(), t)) {
        side = SubstHelper::apply(side, subs);
        head = side.head();
        return true;
      }
    }
    return false;
  }

  void normalize(const Substitution& subs)
  {
    // 1. We want to reach a fixed point of applying the substitution
    // on the head and then beta normalizing it if it's a lambda.
    //
    // TODO this is very inefficient now, we only have to beta normalize
    // any applications on the head.
    bool changed;
    do {
      changed = false;
      auto newLhs = HOL::reduce::betaNF(_lhs);
      if (newLhs != _lhs) {
        changed = true;
        _lhs = newLhs;
        _lhead = _lhs.head();
      }
      auto newRhs = HOL::reduce::betaNF(_rhs);
      if (newRhs != _rhs) {
        changed = true;
        _rhs = newRhs;
        _rhead = _rhs.head();
      }
      if (derefHead(_lhead, _lhs, subs)) {
        changed = true;
      }
      if (derefHead(_rhead, _rhs, subs)) {
        changed = true;
      }
    } while (changed);

    // 2. We then alpha-eta normalize to get the same prefix on both sides.
    HOL::normaliseLambdaPrefixes(_lhs, _rhs);
    _lhead = _lhs.head();
    _rhead = _rhs.head();
  }
};

// Node

Unifier::Node::Node(Literal* lit, Literal* def, unsigned nextVar)
  : _parent(nullptr), _inf(HOL::UnificationInference::DEFINITION), _def(def), _orig(lit), _freshVar(nextVar)
{
  ASS(lit->isEquality());
  ASS(lit->isPositive());

  _cons.emplace(lit->termArg(0), lit->termArg(1), lit->eqArgSort());
}

Unifier::Node::Node(const Node& parent, HOL::UnificationInference inf, unsigned var, TermList binding)
  : Node(parent)
{
  ASS(inf == HOL::UnificationInference::PROJECTION || inf == HOL::UnificationInference::IMITATION);
  _parent = &parent;
  _inf = inf;
  _subs.bindUnbound(var, binding);
}

Unifier::Node::Node(const Node& parent, HOL::UnificationInference inf, Stack<Constraint> cons)
  : _parent(&parent), _inf(inf), _def(parent._def), _orig(parent._orig), _cons(cons), _subs(parent._subs), _freshVar(parent._freshVar)
{
  ASS_EQ(inf, HOL::UnificationInference::DECOMPOSITION);
}

struct IdempotentSubs {
  const Substitution& _subs;
  IdempotentSubs(const Substitution& subs) : _subs(subs) {}
  TermList apply(unsigned var) const {
    auto t = _subs.apply(var);
    if (t.isVar() && t.var() == var) {
      return t;
    }
    return HOL::reduce::betaEtaNF(SubstHelper::apply(t, *this));
  }
};

LiteralStack Unifier::Node::solution() const
{
  const IdempotentSubs subs(_subs);
  LiteralStack res;

  // 1. add flex-flex pairs
  for (const auto& con : _cons) {
    ASS_REP(con.flexFlex(), con);
    ASS_REP(!con._lhs.containsLooseDBIndex(), con);
    ASS_REP(!con._rhs.containsLooseDBIndex(), con);
    res.push(Literal::createEquality(false,
      HOL::reduce::betaEtaNF(SubstHelper::apply(con._lhs, subs)),
      HOL::reduce::betaEtaNF(SubstHelper::apply(con._rhs, subs)),
      con._sort));
    // the sort should survive unification without changing
    ASS_EQ(con._sort, SubstHelper::apply(con._sort, subs));
  }

#if VDEBUG
  if (!checkSolution(res)) {
    const Node* curr = this;
    DBG("solution check failed");
    DBG("lhs ",HOL::reduce::betaEtaNF(SubstHelper::apply(_orig->termArg(0), subs)));
    DBG("rhs ",HOL::reduce::betaEtaNF(SubstHelper::apply(_orig->termArg(1), subs)));
    DBG("flex-flex constraints ",iterTraits(res.iter()).map([](Literal* lit){ return lit->toString(); }).output());
    while (curr) {
      DBG(*curr);
      curr = curr->_parent;
    }
    ASSERTION_VIOLATION;
  }
#endif

  // 2. add the unifier predicate instance
  res.push(SubstHelper::apply(_def, subs));

  return res;
}

bool Unifier::Node::checkSolution(const LiteralStack& ffPairs) const
{
  const IdempotentSubs subs(_subs);
  auto lhs = HOL::reduce::betaEtaNF(SubstHelper::apply(_orig->termArg(0), subs));
  auto rhs = HOL::reduce::betaEtaNF(SubstHelper::apply(_orig->termArg(1), subs));
  HOL::normaliseLambdaPrefixes(lhs, rhs);

  if (ffPairs.isEmpty()) {
    // if there are no flex-flex pairs, we do a simple check
    return lhs == rhs;
  }
  // we only want to add flex-flex pairs when they are needed to make the terms equal
  if (lhs == rhs) {
    DBG("superfluous constraints for equal solved pair ", lhs, " = ", rhs);
    return false;
  }
  std::vector<bool> ffTags(ffPairs.size(), false);
  Stack<std::pair<TermList, TermList>> todo;
  todo.push({ lhs, rhs });

  while (todo.isNonEmpty()) {
    auto [lcurr, rcurr] = todo.pop();
    HOL::normaliseLambdaPrefixes(lcurr, rcurr);
    auto [lh,largs] = HOL::getHeadAndArgs(lcurr);
    auto [rh,rargs] = HOL::getHeadAndArgs(rcurr);

    // either it is a flex-flex pair
    if (lh.isVar() && rh.isVar()) {
      lcurr = HOL::reduce::betaEtaNF(lcurr);
      rcurr = HOL::reduce::betaEtaNF(rcurr);

      bool found = false;
      for (unsigned i = 0; i < ffPairs.size(); i++) {
        auto [lhs, rhs] = ffPairs[i]->eqArgs();
        if ((lcurr == lhs && rcurr == rhs) || (lcurr == rhs && rcurr == lhs)) {
          found = true;
          ffTags[i] = true;
          // break; // TODO filter out duplicates
        }
      }
      if (!found) {
        DBG("flex-flex pair not found ", lcurr, " = ", rcurr);
        return false;
      }
      continue;
    }

    // or the heads must be the same
    if (lh != rh) {
      DBG("non-flex-flex pair found ", lcurr, " = ", rcurr, " with heads ", lh, " and ", rh);
      return false;
    }

    // if heads are the same, recurse to the arguments
    if (largs.size() != rargs.size()) {
      DBG("different number of arguments for ", lcurr, " = ", rcurr);
      return false;
    }
    auto argSorts = HOL::getArgSorts(lcurr);
    TermList matrix;
    TermStack lambdaSorts;
    HOL::getMatrixAndPrefSorts(lcurr, matrix, lambdaSorts);
    for (unsigned i = 0; i < largs.size(); i++) {
      if (largs[i] != rargs[i]) {
        auto lhs = HOL::create::surroundWithLambdas(largs[i], lambdaSorts, argSorts[i], /*fromTop=*/true);
        auto rhs = HOL::create::surroundWithLambdas(rargs[i], lambdaSorts, argSorts[i], /*fromTop=*/true);
        todo.push({ lhs, rhs });
      }
    }
  }

  // check that all flex-flex pairs were used
  for (unsigned i = 0; i < ffTags.size(); i++) {
    if (!ffTags[i]) {
      DBG("flex-flex pair superfluous ", *ffPairs[i]);
      return false;
    }
  }
  return true;
}

std::pair<Stack<Unifier::Node*>,LiteralStack> Unifier::Node::solve()
{
  for (unsigned i = 0; i < _cons.size();) {

    auto& curr = _cons[i];

    DEBUG("trying to solve ", curr);

    // Following the transitions from "Efficient Full Higher-order Unification" from Vukmirovic et al.

    curr.normalize(_subs);

    DEBUG("after normalization ", curr);

    // 4. delete
    if (curr._lhs == curr._rhs) {
      DEBUG("deleted");
      std::swap(curr, _cons.top());
      _cons.pop();
      continue;
    }

    if (curr.rigidRigid()) {
      DEBUG("rigid-rigid ", curr._lhead, " ", curr._rhead);
      if (curr._lhead != curr._rhead) {
        // fail
        DEBUG("fail");
        return { Stack<Node*>(), LiteralStack() };
      }
      return { decompose(i), LiteralStack() };

    } else if (curr.flexRigid()) {
      DEBUG("flex-rigid ", curr._lhead, " ", curr._rhead);
      auto& flexTerm = curr._lhead.isVar() ? curr._lhs : curr._rhs;
      auto& rigidTerm = curr._lhead.isVar() ? curr._rhs : curr._lhs;
      auto bindings = HOL::getProjAndImitBindings(flexTerm, rigidTerm, _freshVar);

      // if there are no bindings for this constraint, fail
      if (bindings.isEmpty()) {
        DEBUG("fail");
        return { Stack<Node*>(), LiteralStack() };
      }

      Stack<Node*> res;
      for (const auto& [binding,inf] : bindings) {
        DEBUG("binding ", flexTerm.head(), " ", b);
        res.push(new Node(*this, inf, flexTerm.head().var(), binding));
      }
      return { res, LiteralStack() };
    }
    // else flex-flex, which we ignore
    i++;
  }
  // we reached this point only if all pairs are flex-flex, so we have a solution
  return { Stack<Node*>(), solution() };
}

Stack<Unifier::Node*> Unifier::Node::decompose(unsigned index) const
{
  DEBUG("decompose");
  auto& curr = _cons[index];
  auto [lhead, largs] = HOL::getHeadAndArgs(curr._lhs);
  auto [rhead, rargs] = HOL::getHeadAndArgs(curr._rhs);
  auto argSorts = HOL::getArgSorts(curr._lhs);
  ASS_EQ(argSorts, HOL::getArgSorts(curr._rhs));
  ASS_G(largs.size(),0);
  ASS_EQ(largs.size(), rargs.size());
  ASS_EQ(largs.size(), argSorts.size());

  Stack<Constraint> cons;
  for (unsigned j = 0; j < _cons.size(); j++) {
    if (index != j) {
      cons.emplace(_cons[j]);
    }
  }
  TermList matrix;
  TermStack lambdaSorts;
  HOL::getMatrixAndPrefSorts(curr._lhs, matrix, lambdaSorts);
#if VDEBUG
  TermStack otherLambdaSorts;
  HOL::getMatrixAndPrefSorts(curr._rhs, matrix, otherLambdaSorts);
  ASS_EQ(lambdaSorts, otherLambdaSorts);
#endif
  for (unsigned j = 0; j < largs.size(); j++) {
    auto lhs = HOL::create::surroundWithLambdas(largs[j], lambdaSorts, argSorts[j], /*fromTop=*/true);
    auto rhs = HOL::create::surroundWithLambdas(rargs[j], lambdaSorts, argSorts[j], /*fromTop=*/true);
    auto sort = lambdaSorts.isEmpty() ? argSorts[j] : SortHelper::getResultSort(lhs.term());
    cons.emplace(lhs, rhs, sort);
  }
  return { new Node(*this, HOL::UnificationInference::DECOMPOSITION, cons) };
}

std::ostream& operator<<(std::ostream& out, const Unifier::Constraint& con) {
  return out << con._lhs << " =? " << con._rhs;
}

std::ostream& operator<<(std::ostream& out, const Unifier::Node& node) {
  return out << *node._def << " <=> {" << node._cons << "} ⋅ σ: " << node._subs << " [" << node._inf << "]";
}

std::ostream& operator<<(std::ostream& out, const Unifier& unif) {
  return out << unif._lit->termArg(0) << " =? " << unif._lit->termArg(1);
}

} // namespace Saturation
