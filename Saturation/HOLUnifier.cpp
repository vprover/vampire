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
 * @file HOLUnifier.cpp
 * Implements class HOLUnifier.
 */

#include "Debug/Assertion.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/Environment.hpp"

#include "HOLUnifier.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Saturation {

// HOLUnifierHandler

bool HOLUnifierHandler::isHolUnifiable(TermList t)
{
  return t.isLambdaTerm() || (t.isApplication() && t.head().isVar());
}

bool isHOLUnificationConstraint(Literal* lit)
{
  if (!lit->isEquality() || lit->isPositive()) {
    return false;
  }
  return HOLUnifierHandler::isHolUnifiable(lit->termArg(0)) || HOLUnifierHandler::isHolUnifiable(lit->termArg(1));
}

HOLUnifierHandler::HOLUnifierHandler(const Options& opt)
: _kNumIter(opt.holUnifierIterations()) { ASS(_kNumIter); }

Clause* HOLUnifierHandler::handleClause(Clause* cl)
{
  ASS(cl->length());

  LiteralStack lits;
  auto def_units = UnitList::empty();

  for (unsigned i = 0; i < cl->length(); i++) {
    auto lit = (*cl)[i];

    if (isHOLUnificationConstraint(lit)) {
      // first unification constraint, push all previous literals
      if (lits.isEmpty()) {
        for (unsigned j = 0; j < i; j++) { lits.push((*cl)[j]); }
      }
      auto [replLit, def] = introduceDefinition(lit);
      lits.push(replLit);
      UnitList::push(def, def_units);
      continue;
    }

    // We started filling the stack, add all literals to it
    if (lits.isNonEmpty()) {
      lits.push(lit);
    }
  }

  if (lits.isNonEmpty()) {
    ASS(def_units);
    UnitList::push(cl, def_units);
    return Clause::fromStack(lits, NonspecificInferenceMany(InferenceRule::HOL_UNIFIER_ELIMINATION, def_units));
  }
  return cl;
}

ClauseStack HOLUnifierHandler::iterate()
{
  ClauseStack res;

  // do num-many iterations
  for (unsigned j = 0; j < _kNumIter; j++) {

    if (_todo.isEmpty()) {
      return res;
    }

    // circulate inside _todos
    if (_index >= _todo.size()) {
      _index = 0;
    }

    auto& curr = _todo[_index];

    LiteralStack solution;
    if (curr.iterate(solution)) {
      _solved.push(_todo.swapRemove(_index));
    } else {
      _index++;
    }

    if (solution.isNonEmpty()) {
      res.push(Clause::fromStack(solution, NonspecificInference0(UnitInputType::AXIOM, InferenceRule::HOL_UNIFIER_SOLUTION)));
    }
  }
  return res;
}

std::pair<Literal*,Unit*> HOLUnifierHandler::introduceDefinition(Literal* lit)
{
  ASS(isHOLUnificationConstraint(lit));

  Renaming r;
  r.normalizeVariables(lit);
  auto nlit = Literal::complementaryLiteral(r.apply(lit));

  // 1. collect variable sorts
  DHSet<unsigned> varsSeen;
  TermStack typeVars;
  Stack<std::pair<TermList, TermList>> termVars;
  TermStack termVarSorts;

  for (const auto& [v,sort] : iterTraits(VariableWithSortIterator(lit))) {
    if (varsSeen.insert(v.var())) {
      if (sort.isTerm() && sort.term()->isSuper()) {
        typeVars.push(v);
      } else {
        termVars.push({ v, sort });
        termVarSorts.push(sort);
      }
    }
  }

  UCDef* def_ptr;

  // 2. introduce definition if needed

  if (_litToDefMap.getValuePtr(nlit, def_ptr)) {

    // 2.1. introduce predicate based on variables
    auto p = env.signature->addFreshPredicate(varsSeen.size(), "p_hol");
    auto sym = env.signature->getPredicate(p);
    SortHelper::normaliseArgSorts(typeVars, termVarSorts);
    auto type = OperatorType::getPredicateType(termVarSorts.size(), termVarSorts.begin(), typeVars.size());
    sym->setType(type);

    // 2.2. add definition

    TermStack p_args;
    auto vl = VSList::empty();
    for (const auto& v : typeVars) {
      auto vr = r.apply(v);
      p_args.push(vr);
      VSList::push({ vr.var(), AtomicSort::superSort() }, vl);
    }
    for (const auto& [v,s] : termVars) {
      auto vr = r.apply(v);
      auto sr = r.apply(s);
      p_args.push(vr);
      VSList::push({ vr.var(), sr }, vl);
    }

    auto plit = Literal::create(p, /*arity=*/p_args.size(), /*polarity=*/true, p_args.begin());

    Formula* def = new BinaryFormula(Connective::IFF, new AtomicFormula(plit), new AtomicFormula(nlit));
    if (vl) {
      def = new QuantifiedFormula(Connective::FORALL, vl, def);
    }
    auto def_u = new FormulaUnit(def, NonspecificInference0(UnitInputType::AXIOM,InferenceRule::HOL_UNIFIER_DEFINITION));

    if (env.options->showAll()) {
      std::cout << "[HOL] introduced definition " << def->toString() << std::endl;
    }

    _todo.emplace(nlit, plit, r.nextVar());

    *def_ptr = { p, def_u };
  }

  // 3. create new literal
  auto p_s_args = TermStack::fromIterator(typeVars.iterFifo());
  p_s_args.loadFromIterator(iterTraits(termVars.iterFifo()).map([](auto kv){ return kv.first; }));
  return { Literal::create(def_ptr->pred, /*arity=*/p_s_args.size(), /*polarity=*/false, p_s_args.begin()), def_ptr->def };
}

// HOLUnifier

HOLUnifier::HOLUnifier(Literal* lit, Literal* def, unsigned nextVar)
  : _todo({ new Node(lit, def, nextVar )}) {}

bool HOLUnifier::iterate(LiteralStack& solution)
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

struct HOLUnifier::Constraint
{
  TermList _lhs;
  TermList _rhs;
  TermList _lhead;
  TermList _rhead;

  Constraint(TermList lhs, TermList rhs)
    : _lhs(lhs), _rhs(rhs), _lhead(lhs.head()), _rhead(rhs.head())
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
    do {
      // 1. alpha-eta normalize
      HOL::normaliseLambdaPrefixes(_lhs, _rhs);

      // 2. betaNormalize
      // TODO this is probably not needed, but maybe easier to do it here lazily
      _lhs = HOL::reduce::betaNF(_lhs);
      _lhead = _lhs.head();
      _rhs = HOL::reduce::betaNF(_rhs);
      _rhead = _rhs.head();

      // 3. dereference
    } while (derefHead(_lhead, _lhs, subs) || derefHead(_rhead, _rhs, subs));
  }
};

// Node

HOLUnifier::Node::Node(Literal* lit, Literal* def, unsigned nextVar)
  : _def(def), _freshVar(nextVar)
{
  ASS(lit->isEquality());
  ASS(lit->isPositive());

  _cons.emplace(lit->termArg(0), lit->termArg(1));
}

HOLUnifier::Node::Node(const Node& parent, unsigned var, TermList binding)
  : Node(parent)
{
  _subs.bindUnbound(var, binding);
}

HOLUnifier::Node::Node(const Node& parent, Stack<Constraint> cons)
  : _def(parent._def), _cons(cons), _subs(parent._subs), _freshVar(parent._freshVar)
{
}

LiteralStack HOLUnifier::Node::solution()
{
  struct IdempotentSubs {
    const Substitution& _subs;
    IdempotentSubs(const Substitution& subs) : _subs(subs) {}
    TermList apply(unsigned var) {
      auto t = _subs.apply(var);
      if (t.isVar() && t.var() == var) {
        return t;
      }
      return HOL::reduce::betaNF(SubstHelper::apply(t, *this));
    }
  };

  IdempotentSubs subs(_subs);
  LiteralStack res;

  res.push(SubstHelper::apply(_def, subs));
  for (const auto& con : _cons) {
    ASS(con.flexFlex());
    res.push(Literal::createEquality(false,
      SubstHelper::apply(con._lhs, subs), SubstHelper::apply(con._rhs, subs),
      SortHelper::getResultSort(con._lhs.term())));
  }
  return res;
}

std::pair<Stack<HOLUnifier::Node*>,LiteralStack> HOLUnifier::Node::solve()
{
  Stack<Node*> res;

  for (unsigned i = 0; i < _cons.size();) {

    auto& curr = _cons[i];

    DEBUG("trying to solve ", curr);

    // Following the transitions from "Efficient Full Higher-order Unification" from Vukmirovic et al.

    curr.normalize(_subs);

    DEBUG("after normalization ", curr);

    // 4. delete
    if (curr._lhs == curr._rhs) {
      std::swap(curr, _cons.top());
      _cons.pop();
      continue;
    }

    if (curr.rigidRigid()) {
      if (curr._lhead != curr._rhead) {
        // fail
        return { Stack<Node*>(), LiteralStack() };
      }

      DEBUG("decompose");
      if (curr._lhs.isApplication()) {
        ASS(curr._rhs.isApplication());
        auto [lhead, largs] = HOL::getHeadAndArgs(curr._lhs);
        auto [rhead, rargs] = HOL::getHeadAndArgs(curr._rhs);
        ASS_EQ(largs.size(), rargs.size());

        Stack<Constraint> cons;
        for (unsigned i = 0; i < largs.size(); i++) {
          cons.emplace(largs[i], rargs[i]);
        }
        res.push(new Node(*this, cons));
      } else {
        ASSERTION_VIOLATION;
      }
    } else if (curr.flexRigid()) {
      auto& flexTerm = curr._lhead.isVar() ? curr._lhs : curr._rhs;
      auto& rigidTerm = curr._lhead.isVar() ? curr._rhs : curr._lhs;
      TermStack bindings = HOL::getProjAndImitBindings(flexTerm, rigidTerm, _freshVar);

      for (const auto& b : bindings) {
        DEBUG("binding ", flexTerm.head(), " ", b);
        res.push(new Node(*this, flexTerm.head().var(), b));
      }
    }
    i++;
  }
  if (res.isEmpty()) {
    return { res, solution() };
  }
  return { res, LiteralStack() };
}

std::ostream& operator<<(std::ostream& out, const HOLUnifier::Constraint& con) {
  return out << con._lhs << " = " << con._rhs;
}

std::ostream& operator<<(std::ostream& out, const HOLUnifier::Node& node) {
  return out << node._cons << " " << node._subs;
}

} // namespace Saturation
