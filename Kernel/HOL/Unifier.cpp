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
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"

#include "Unifier.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace HOL {

// UnifierNode

std::ostream& operator<<(std::ostream& out, const UnificationNode::Constraint& con) {
  return out << con._lhs << " =?= " << con._rhs;
}

std::ostream& operator<<(std::ostream& out, const UnificationNode& node) {
  return out << "{" << node._cons << "} ⋅ σ: " << node._subs;
}

UnificationNode::Constraint::Constraint(TermList lhs, TermList rhs, TermList sort)
  : _lhs(lhs), _rhs(rhs), _sort(sort), _lhead(lhs.head()), _rhead(rhs.head())
{
  // terms must be in whnf
  ASS_REP(!_lhead.isLambdaTerm(), _lhead.toString());
  ASS_REP(!_rhead.isLambdaTerm(), _rhead.toString());
}

bool UnificationNode::Constraint::derefHead(TermList& head, TermList& side, const Substitution& subs)
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

void UnificationNode::Constraint::normalize(const Substitution& subs)
{
  // 1. We want to reach a fixed point of applying the substitution
  // on the head and then beta normalizing it if it's a lambda.
  //
  // TODO this is very inefficient now, we only have to beta normalize
  // any applications on the head. Use WHNF from the HOL branch.
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

// Node

UnificationNode::UnificationNode(Stack<UnificationNode::Constraint> cons, unsigned nextVar)
  : _cons(cons), _freshVar(nextVar)
{}

UnificationNode::UnificationNode(const UnificationNode& parent, unsigned var, TermList binding)
  : UnificationNode(parent)
{
  _subs.bindUnbound(var, binding);
}

UnificationNode::UnificationNode(const UnificationNode& parent, Stack<UnificationNode::Constraint> cons)
  : _cons(cons), _subs(parent._subs), _freshVar(parent._freshVar)
{}

Option<Stack<UnificationNode*>> UnificationNode::solve()
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
        return none<Stack<UnificationNode*>>();
      }
      return some<Stack<UnificationNode*>>({ new UnificationNode(*this, decompose(i, /*includeRest=*/true)) });

    } else if (curr.flexRigid()) {
      DEBUG("flex-rigid ", curr._lhead, " ", curr._rhead);
      auto& flexTerm = curr._lhead.isVar() ? curr._lhs : curr._rhs;
      auto& rigidTerm = curr._lhead.isVar() ? curr._rhs : curr._lhs;
      auto bindings = HOL::getProjAndImitBindings(flexTerm, rigidTerm, _freshVar);

      // if there are no bindings for this constraint, fail
      if (bindings.isEmpty()) {
        DEBUG("fail");
        return none<Stack<UnificationNode*>>();
      }

      Stack<UnificationNode*> res;
      for (const auto& [binding,inf] : bindings) {
        DEBUG("binding ", flexTerm.head(), " ", binding);
        res.push(new UnificationNode(*this, flexTerm.head().var(), binding));
      }
      return some<Stack<UnificationNode*>>(res);
    }
    // else flex-flex, which we ignore
    i++;
  }
  // we reached this point only if all pairs are flex-flex, so we have a solution
  return some<Stack<UnificationNode*>>(Stack<UnificationNode*>());
}

bool UnificationNode::simplify()
{
  for (unsigned i = 0; i < _cons.size();) {

    auto& curr = _cons[i];

    DEBUG("trying to simplify ", curr);

    // Following the transitions from "Efficient Full Higher-order Unification" from Vukmirovic et al.

    curr.normalize(_subs);

    DEBUG("after normalization ", curr);

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
        return false;
      }
      auto dc = decompose(i, /*includeRest=*/false);
      std::swap(curr, _cons.top());
      _cons.pop();
      for (auto&& con : std::move(dc)) {
        DEBUG("decomposed ", con);
        _cons.push(con);
      }
      continue;
    }
    // else ignore flex-flex or flex-rigid
    i++;
  }
  return true;
}

Stack<UnificationNode::Constraint> UnificationNode::decompose(unsigned index, bool includeRest) const
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

  Stack<UnificationNode::Constraint> cons;
  if (includeRest) {
    for (unsigned j = 0; j < _cons.size(); j++) {
      if (index != j) {
        cons.emplace(_cons[j]);
      }
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
  return cons;
}

AbstractingWrapper::AbstractingWrapper(AbstractingUnifier* unifier, unsigned hoUnifDepth)
  : _unifier(new AbstractingUnifier(unifier->_uwa)), _hoUnifDepth(hoUnifDepth)
{
  _unifier->subs().copy(unifier->subs());
  Stack<UnificationNode::Constraint> cons;
  for (const auto c : unifier->constr().iter()) {
    cons.emplace(
      c.lhs().toGluedTerm(_unifier->subs()),
      c.rhs().toGluedTerm(_unifier->subs()),
      c.sort().toGluedTerm(_unifier->subs())
    );
  }
  _todo.emplace(new UnificationNode(cons, _unifier->subs().nextGlueVar()), 0);
}

AbstractingWrapper::~AbstractingWrapper()
{
  delete _next;
  delete _unifier;
}

bool AbstractingWrapper::hasNext()
{
  if (_next) {
    return true;
  }
  while (_todo.isNonEmpty()) {
    auto [node, depth] = _todo.pop();

    DEBUG("curr node at depth ", depth, ": ", *node);

    if (!node->simplify()) {
      DEBUG("simplification failed");
      delete node;
      continue;
    }

    if (depth >= _hoUnifDepth) {
      DEBUG("reached maximal depth");
      _next = node;
      return true;
    }

    auto res = node->solve();
    if (res.isNone()) {
      DEBUG("solving failed");
      delete node;
      continue;
    }

    if (res->isEmpty()) {
      DEBUG("trivially solved");
      _next = node;
      return true;
    }

    DEBUG("has children");
    for (const auto& n : *res) {
      _todo.emplace(n, depth+1);
    }
    delete node;
  }
  return false;
}

AbstractingUnifier* AbstractingWrapper::next()
{
  ASS(_next);
  DEBUG("about to return extended abstracting unifier ", *_unifier);
  _localBD.backtrack();
  DEBUG("backtracked from previous state ", *_unifier);

  _unifier->subs().bdRecord(_localBD);
  for (const auto& [v, t] : iterTraits(_next->_subs.items())) {
    ALWAYS(_unifier->subs().unify(TermList::var(v), GLUE_INDEX, t, GLUE_INDEX));
  }
  _unifier->subs().bdDone();

  _unifier->constr().reset();
  for (const auto& con : _next->_cons) {
    ASS_REP(con.flexFlex() || con.flexRigid(), con);
    ASS_REP(!con._lhs.containsLooseDBIndex(), con);
    ASS_REP(!con._rhs.containsLooseDBIndex(), con);
    auto sortS = SubstHelper::apply(con._sort, _next->_subs);
    // the sort should survive unification without changing
    ASS_EQ(con._sort, sortS);

    TermSpec lhs(HOL::reduce::betaEtaNF(SubstHelper::apply(con._lhs, _next->_subs)), GLUE_INDEX);
    TermSpec rhs(HOL::reduce::betaEtaNF(SubstHelper::apply(con._rhs, _next->_subs)), GLUE_INDEX);
    DEBUG("adding constraint ", lhs, " != ", rhs);
    _unifier->constr().add(UnificationConstraint(lhs, rhs, TermSpec(SubstHelper::apply(con._sort, _next->_subs), GLUE_INDEX)), _localBD);
  }

  delete _next;
  _next = nullptr;
  return _unifier;
}

} // namespace HOL
