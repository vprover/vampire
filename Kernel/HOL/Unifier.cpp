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
#include "Kernel/HOL/EtaNormaliser.hpp"

#include "Unifier.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace HOL {

namespace {

TermList deref(TermList t, const Substitution& subs)
{
  while (t.isVar()) {
    TermList out;
    if (!subs.findBinding(t.var(), out)) {
      break;
    }
    t = out;
  }
  return t;
}

bool occurs(unsigned var, TermList t, const Substitution& subs)
{
  Stack<TermList> todo;
  todo.push(t);

  while (todo.isNonEmpty()) {
    auto curr = deref(todo.pop(), subs);
    if (curr.isVar()) {
      if (var == curr.var()) {
        return true;
      }
      continue;
    }
    for (const auto& arg : anyArgIter(curr.term())) {
      todo.push(arg);
    }
  }
  return false;
}

bool unifyHeads(Term* t1, Term* t2, Substitution& subs)
{
  DEBUG("unifying heads ", *t1, " and ", *t2);
  if (t1->functor() != t2->functor()) {
    return false;
  }
  ASS(!t1->numTermArguments());

  SubtermIterator stit1(t1);
  SubtermIterator stit2(t2);
  while (stit1.hasNext()) {
    ALWAYS(stit2.hasNext());
    auto st1 = deref(stit1.next(), subs);
    auto st2 = deref(stit2.next(), subs);
    if (st1 == st2) {
      stit1.right();
      stit2.right();
      continue;
    }
    if (st1.isVar() && !occurs(st1.var(), st2, subs)) {
      subs.bindUnbound(st1.var(), st2);
      stit2.right();
    } else if (st2.isVar() && !occurs(st2.var(), st1, subs)) {
      subs.bindUnbound(st2.var(), st1);
      stit1.right();
    } else if (st1.isTerm() && st2.isTerm() && st1.term()->functor() == st2.term()->functor()) {
      continue;
    } else {
      return false;
    }
  }
  return true;
}

}

// UnifierNode

std::ostream& operator<<(std::ostream& out, const UnificationNode::Constraint& con) {
  return out << con._lhs << " =?= " << con._rhs;
}

std::ostream& operator<<(std::ostream& out, const UnificationNode& node) {
  return out << "{" << node._cons << "} ⋅ σ: " << node._subs;
}

UnificationNode::Constraint::Constraint(TermList lhs, TermList rhs, TermList sort)
  : _lhs(lhs), _rhs(rhs), _sort(sort)
{
  ASS(_lhs.isVar() || SortHelper::getResultSort(_lhs.term()) == _sort);
  ASS(_rhs.isVar() || SortHelper::getResultSort(_rhs.term()) == _sort);
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

void UnificationNode::Constraint::normalize(TermList& head, TermList& side, const Substitution& subs)
{
  while (true) {
    auto newSide = HOL::reduce::betaNF(side);
    if (newSide != side) {
      side = newSide;
      head = side.head();
      derefHead(head, side, subs);
      continue;
    }
    if (derefHead(head, side, subs)) {
      continue;
    }
    break;
  }
}

void UnificationNode::Constraint::normalize(const Substitution& subs)
{
  // We want to reach a fixed point of applying the substitution
  // on the head and then beta normalizing it if it's a lambda.
  //
  // TODO this is very inefficient now, we only have to beta normalize
  // any applications on the head. Use WHNF from the HOL branch.
  normalize(_lhead, _lhs, subs);
  normalize(_rhead, _rhs, subs);

  // We then alpha-eta normalize to get the same prefix on both sides.
  HOL::normaliseLambdaPrefixes(_lhs, _rhs);
  _lhead = _lhs.head();
  _rhead = _rhs.head();
}

// Node

UnificationNode::UnificationNode(Stack<UnificationNode::Constraint> cons, unsigned nextVar, bool funcExt)
  : _cons(cons), _freshVar(nextVar), _funcExt(funcExt)
{}

UnificationNode::UnificationNode(const UnificationNode& parent, unsigned var, TermList binding)
  : UnificationNode(parent)
{
  _subs.bindUnbound(var, binding);
}

UnificationNode::UnificationNode(const UnificationNode& parent, Stack<UnificationNode::Constraint> cons)
  : _cons(cons), _subs(parent._subs), _freshVar(parent._freshVar), _funcExt(parent._funcExt)
{}

Option<Stack<UnificationNode*>> UnificationNode::solve()
{
  for (unsigned i = 0; i < _cons.size();) {

    auto& curr = _cons[i];

    DEBUG("trying to solve ", curr);

    curr.normalize(_subs);

    DEBUG("after normalization ", curr);

    // trivial constraint, delete
    if (curr._lhs == curr._rhs) {
      DEBUG("deleted");
      _cons.swapRemove(i);
      continue;
    }

    // TODO(HOL): if simplify is called, this should be unnecessary
    if (curr.rigidRigid()) {
      DEBUG("rigid-rigid ", curr._lhead, " ", curr._rhead);
      if (_funcExt && curr._sort.isExtensionalSort()) {
        DEBUG("extensionality with sort ", curr._sort);
        i++;
        continue;
      }
      if (!unifyHeads(curr._lhead.term(), curr._rhead.term(), _subs)) {
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
    ASS(curr.flexFlex());
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

    curr.normalize(_subs);

    DEBUG("after normalization ", curr);

    if (curr._lhs == curr._rhs) {
      DEBUG("deleted");
      _cons.swapRemove(i);
      continue;
    }

    if (curr.rigidRigid()) {
      DEBUG("rigid-rigid ", curr._lhead, " ", curr._rhead);
      if (_funcExt && curr._sort.isExtensionalSort()) {
        DEBUG("extensionality with sort ", curr._sort);
        i++;
        continue;
      }
      if (!unifyHeads(curr._lhead.term(), curr._rhead.term(), _subs)) {
        // fail
        DEBUG("fail");
        return false;
      }
      auto dc = decompose(i, /*includeRest=*/false);
      _cons.swapRemove(i);
      for (auto&& con : std::move(dc)) {
        DEBUG("decomposed ", con);
        _cons.push(con);
      }
      continue;
    }

    if (curr.flexRigid()) {
      auto res = fixpointUnify(curr);
      if (res == OracleResult::FAILURE) {
        DEBUG("oracle fail");
        return false;
      } else if (res == OracleResult::SUCCESS) {
        DEBUG("oracle success");
        _cons.swapRemove(i);
        i = 0; // TODO(HOL): maybe starting over is not necessary
        continue;
      }
    }

    // else ignore flex-flex or flex-rigid
    ASS(curr.flexFlex() || curr.flexRigid());
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
  // check that the type args are the same modulo current substitution
  ASS(iterTraits(argSorts.iter()).zip(HOL::getArgSorts(curr._rhs).iter()).all([&](auto arg) {
    return SubstHelper::apply(arg.first, _subs) == SubstHelper::apply(arg.second, _subs);
  }));
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
    auto argSort = SubstHelper::apply(argSorts[j], _subs);
    auto lhs = HOL::create::surroundWithLambdas(SubstHelper::apply(largs[j], _subs), lambdaSorts, argSort, /*fromTop=*/true);
    auto rhs = HOL::create::surroundWithLambdas(SubstHelper::apply(rargs[j], _subs), lambdaSorts, argSort, /*fromTop=*/true);
    auto sort = lambdaSorts.isEmpty() ? argSort : SortHelper::getResultSort(lhs.term());
    cons.emplace(lhs, rhs, sort);
  }
  return cons;
}

// Given unification pair {F ?= t}, if F does not occur in t, {F ↦ t} is an MGU for the problem.
// If there is a position p in t such that t|p = F u_m and for each prefix q != p of p, t|q has
// a rigid head and either m = 0 or t is not a λ-abstraction, then F ?= t has no solutions.
// Otherwise, the fixpoint oracle is not applicable.
UnificationNode::OracleResult UnificationNode::fixpointUnify(Constraint con)
{
  ASS(con.flexRigid());
  // TODO probably shouldn't normalize again here
  con.normalize(_subs);

  auto flex = con._lhead.isVar() ? con._lhs : con._rhs;
  auto rigid = con._lhead.isVar() ? con._rhs : con._lhs;
  flex = EtaNormaliser::normalise(flex);
  if (flex.isTerm()) {
    return OracleResult::OUT_OF_FRAGMENT;
  }

  bool tIsLambda = rigid.isLambdaTerm();
  if (rigid.isVar()) {
    _subs.bind(flex.var(), rigid);
    return OracleResult::SUCCESS;
  }

  // stack of <term, underFlex, depth> tuples
  Recycled<Stack<std::tuple<TermList, bool, unsigned>>> todo;
  todo->emplace(rigid, false, 0);

  while (todo->isNonEmpty()){
    auto [t, underFlex, depth] = todo->pop();
    auto head = t.head();
    con.normalize(head, t, _subs);

    // TODO consider adding an encountered store similar to first-order occurs check...

    while (t.isLambdaTerm()) {
      t = t.lambdaBody();
      depth++;
    }

    TermStack args;
    head = HOL::getHeadAndArgs(t, args);

    ASS(!head.isLambdaTerm());
    if (head.isVar() && head == flex) {
      return (underFlex || (tIsLambda && args.size())) ? OracleResult::OUT_OF_FRAGMENT : OracleResult::FAILURE;
    }

    auto dbi = head.deBruijnIndex();
    if (dbi.isSome() && *dbi >= depth) {
      // contains a free index, cannot bind
      return underFlex ? OracleResult::OUT_OF_FRAGMENT : OracleResult::FAILURE;
    }

    bool argsUnderFlex = head.isVar() || underFlex;
    for (const auto& arg : args) {
      todo->emplace(arg, argsUnderFlex, depth);
    }
  }

  _subs.bind(flex.var(), rigid);
  return OracleResult::SUCCESS;
}

AbstractingWrapper::AbstractingWrapper(AbstractingUnifier* unifier, unsigned hoUnifDepth, bool funcExt)
  : _unifier(new AbstractingUnifier(unifier->_uwa)), _hoUnifDepth(hoUnifDepth)
#if VDEBUG
  , _funcExt(funcExt)
#endif
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
  _todo.emplace(new UnificationNode(cons, _unifier->subs().nextGlueVar(), funcExt), 0);
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
  _localBD.backtrack();
  DEBUG("backtracked from previous state ", *_unifier);

  _unifier->subs().bdRecord(_localBD);
  for (const auto& [v, t] : iterTraits(_next->_subs.items())) {
    ALWAYS(_unifier->subs().unify(TermList::var(v), GLUE_INDEX, t, GLUE_INDEX));
  }
  _unifier->subs().bdDone();

  _unifier->constr().reset();
  for (const auto& con : _next->_cons) {
    ASS_REP(con.flexFlex() || con.flexRigid() || (_funcExt && (con._sort.isArrowSort() || con._sort.isBoolSort())), con);
    ASS_REP(!con._lhs.containsLooseDBIndex(), con);
    ASS_REP(!con._rhs.containsLooseDBIndex(), con);
    auto sortS = SubstHelper::apply(con._sort, _next->_subs);
    // the sort should survive unification without changing
    ASS_EQ(con._sort, sortS);

    TermSpec lhs(HOL::reduce::betaEtaNF(SubstHelper::apply(con._lhs, _next->_subs)), GLUE_INDEX);
    TermSpec rhs(HOL::reduce::betaEtaNF(SubstHelper::apply(con._rhs, _next->_subs)), GLUE_INDEX);
    DEBUG("adding constraint ", lhs, " != ", rhs);
    _unifier->constr().add(UnificationConstraint(lhs, rhs, TermSpec(sortS, GLUE_INDEX)), _localBD);
  }
  DEBUG("about to return extended abstracting unifier ", *_unifier);

  delete _next;
  _next = nullptr;
  return _unifier;
}

} // namespace HOL
