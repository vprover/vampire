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
#include "Kernel/UnificationWithAbstraction.hpp"

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

bool Unifier::simplify(LiteralStack& solution)
{
  ASS(solution.isEmpty());

  ASS_EQ(_todo.size(),1);

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

TermList Unifier::applyTermSpec(TermSpec t, RobSubstitution& subs, DHMap<VarSpec,unsigned>& varMap)
{
  return HOL::reduce::betaEtaNF(BottomUpEvaluation<AutoDerefTermSpec, TermList>()
    .function([&subs,&varMap](auto const& orig, TermList* args) -> TermList {
      if (orig.term.isVar()) {
        ASS(!orig.term.varSpec().special());
        unsigned* ptr;
        if (varMap.getValuePtr(orig.term.varSpec(), ptr, 0)) {
          *ptr = subs.introGlueVar(orig.term.varSpec()).var();
        }
        return TermList::var(*ptr);
      }
      return TermList(orig.term.isSort() ? AtomicSort::create(orig.term.functor(), orig.term.nAllArgs(), args)
        : Term::create(orig.term.functor(), orig.term.nAllArgs(), args));
    })
    .evNonRec([](auto& t) { return someIf(t.term.definitelyGround(), [&]() { return t.term.term; }); })
    .context(AutoDerefTermSpec::Context { .subs = &subs, })
    .apply(AutoDerefTermSpec(t, &subs)));
}

// Constraint

Unifier::Constraint::Constraint(TermList lhs, TermList rhs, TermList sort)
  : _lhs(lhs), _rhs(rhs), _sort(sort), _lhead(lhs.head()), _rhead(rhs.head())
{
  // terms must be in whnf
  ASS_REP(!_lhead.isLambdaTerm(), _lhead.toString());
  ASS_REP(!_rhead.isLambdaTerm(), _rhead.toString());
}

bool Unifier::Constraint::derefHead(TermList& head, TermList& side, const Substitution& subs)
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

void Unifier::Constraint::normalize(const Substitution& subs)
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
      return { { new Node(*this, HOL::UnificationInference::DECOMPOSITION, decompose(i, /*includeRest=*/true)) }, LiteralStack() };

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
        DEBUG("binding ", flexTerm.head(), " ", binding);
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

bool Unifier::Node::simplify()
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
        _cons.push(con);
      }
      continue;
    }
    // else ignore flex-flex or flex-rigid
    i++;
  }
  return true;
}

Recycled<Stack<UnificationConstraint>> Unifier::Node::toUnif() const
{
  const IdempotentSubs subs(_subs);
  Recycled<Stack<UnificationConstraint>> res;

  for (const auto& con : _cons) {
    ASS_REP(con.flexFlex() || con.flexRigid(), con);
    ASS_REP(!con._lhs.containsLooseDBIndex(), con);
    ASS_REP(!con._rhs.containsLooseDBIndex(), con);
    res->emplace(
      TermSpec(HOL::reduce::betaEtaNF(SubstHelper::apply(con._lhs, subs)), GLUE_INDEX),
      TermSpec(HOL::reduce::betaEtaNF(SubstHelper::apply(con._rhs, subs)), GLUE_INDEX),
      TermSpec(SubstHelper::apply(con._sort, subs), GLUE_INDEX)
    );
    // the sort should survive unification without changing
    ASS_EQ(con._sort, SubstHelper::apply(con._sort, subs));
  }

  return res;
}

Stack<Unifier::Constraint> Unifier::Node::decompose(unsigned index, bool includeRest) const
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

std::ostream& operator<<(std::ostream& out, const Unifier::Constraint& con) {
  return out << con._lhs << " =? " << con._rhs;
}

std::ostream& operator<<(std::ostream& out, const Unifier::Node& node) {
  return out << *node._def << " <=> {" << node._cons << "} ⋅ σ: " << node._subs << " [" << node._inf << "]";
}

std::ostream& operator<<(std::ostream& out, const Unifier& unif) {
  return out << unif._lit->termArg(0) << " =? " << unif._lit->termArg(1);
}



//// New stuff

std::ostream& operator<<(std::ostream& out, const WrapperConstraint& con) {
  return out << con._lhs << " =?= " << con._rhs;
}

std::ostream& operator<<(std::ostream& out, const WrapperNode& node) {
  return out << "{" << node._cons << "} ⋅ σ: " << node._subs;
}

WrapperConstraint::WrapperConstraint(TermList lhs, TermList rhs, TermList sort)
  : _lhs(lhs), _rhs(rhs), _sort(sort), _lhead(lhs.head()), _rhead(rhs.head())
{
  // terms must be in whnf
  ASS_REP(!_lhead.isLambdaTerm(), _lhead.toString());
  ASS_REP(!_rhead.isLambdaTerm(), _rhead.toString());
}

bool WrapperConstraint::derefHead(TermList& head, TermList& side, const Substitution& subs)
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

void WrapperConstraint::normalize(const Substitution& subs)
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

WrapperNode::WrapperNode(Stack<WrapperConstraint> cons, unsigned nextVar)
  : _cons(cons), _freshVar(nextVar)
{}

WrapperNode::WrapperNode(const WrapperNode& parent, unsigned var, TermList binding)
  : WrapperNode(parent)
{
  _subs.bindUnbound(var, binding);
}

WrapperNode::WrapperNode(const WrapperNode& parent, Stack<WrapperConstraint> cons)
  : _cons(cons), _subs(parent._subs), _freshVar(parent._freshVar)
{}

Option<Stack<WrapperNode*>> WrapperNode::solve()
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
        return none<Stack<WrapperNode*>>();
      }
      return some<Stack<WrapperNode*>>({ new WrapperNode(*this, decompose(i, /*includeRest=*/true)) });

    } else if (curr.flexRigid()) {
      DEBUG("flex-rigid ", curr._lhead, " ", curr._rhead);
      auto& flexTerm = curr._lhead.isVar() ? curr._lhs : curr._rhs;
      auto& rigidTerm = curr._lhead.isVar() ? curr._rhs : curr._lhs;
      auto bindings = HOL::getProjAndImitBindings(flexTerm, rigidTerm, _freshVar);

      // if there are no bindings for this constraint, fail
      if (bindings.isEmpty()) {
        DEBUG("fail");
        return none<Stack<WrapperNode*>>();
      }

      Stack<WrapperNode*> res;
      for (const auto& [binding,inf] : bindings) {
        DEBUG("binding ", flexTerm.head(), " ", binding);
        res.push(new WrapperNode(*this, flexTerm.head().var(), binding));
      }
      return some<Stack<WrapperNode*>>(res);
    }
    // else flex-flex, which we ignore
    i++;
  }
  // we reached this point only if all pairs are flex-flex, so we have a solution
  return some<Stack<WrapperNode*>>(Stack<WrapperNode*>());
}

bool WrapperNode::simplify()
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

Stack<WrapperConstraint> WrapperNode::decompose(unsigned index, bool includeRest) const
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

  Stack<WrapperConstraint> cons;
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
  : _unifier(unifier), _hoUnifDepth(hoUnifDepth)
{
  Stack<WrapperConstraint> cons;
  for (const auto c : _unifier->constr().iter()) {
    cons.emplace(
      c.lhs().toGluedTerm(_unifier->subs()),
      c.rhs().toGluedTerm(_unifier->subs()),
      c.sort().toGluedTerm(_unifier->subs())
    );
  }
  _todo.emplace(new WrapperNode(cons, _unifier->subs().nextGlueVar()), 0);
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
