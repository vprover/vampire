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
 * @file FasterCondensation.cpp
 * Implements class FasterCondensation.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include <deque>

#include "FasterCondensation.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

TermList deref(TermList t, const Substitution& subst)
{
  while (t.isVar()) {
    TermList res;
    if (!subst.findBinding(t.var(), res)) {
      break;
    }
    t = res;
  }
  return t;
}

bool occurs(unsigned var, TermList t, const Substitution& subst)
{
  Recycled<DHSet<TermList>> encountered;
  Recycled<Stack<TermList>> todo;
  todo->push(t);

  while (todo->isNonEmpty()){
    auto dt = deref(todo->pop(), subst);
    if (!encountered->find(dt)) {
      encountered->insert(dt);
      if (dt.isVar()) {
        if(dt.var() == var) {
          return true;
        }
      } else {
        todo->loadFromIterator(anyArgIter(dt.term()));
      }
    }
  }

  return false;
}

// TODO implement equality unification properly
bool unify(Literal* lit, Literal* other, Substitution& subst, bool canBind)
{
  ASS_NEQ(lit, other);
  if (lit->header() != other->header()) {
    return false;
  }

  Stack<std::pair<TermList, TermList>> todo;
  for (unsigned i = 0; i < lit->arity(); i++) {
    todo.emplace(*lit->nthArgument(i), *other->nthArgument(i));
  }

  // Save encountered unification pairs to avoid
  // recomputing their unification
  DHSet<std::pair<TermList, TermList>> encountered;

  while (todo.isNonEmpty()) {
    auto [lhs, rhs] = todo.pop();
    auto dt1 = deref(lhs, subst);
    auto dt2 = deref(rhs, subst);
    if (dt1 == dt2) {
    } else if(dt1.isVar() && canBind && !occurs(dt1.var(), dt2, subst)) {
      subst.bindUnbound(dt1.var(), dt2);
    } else if(dt2.isVar() && canBind && !occurs(dt2.var(), dt1, subst)) {
      subst.bindUnbound(dt2.var(), dt1);
    } else if(dt1.isTerm() && dt2.isTerm() && dt1.term()->functor() == dt2.term()->functor()) {

      for (unsigned i = 0; i < dt1.term()->arity(); i++) {
        auto pair = std::make_pair(*dt1.term()->nthArgument(i), *dt2.term()->nthArgument(i));
        if (encountered.insert(pair)) {
          todo.emplace(pair);
        }
      }

    } else {
      return false;
    }
  }
  return true;
}

bool instantiated(Literal* lit, const Substitution& subst)
{
  DEBUG("instantiated ", *lit);
  return iterTraits(VariableIterator(lit)).any([&subst](TermList var) {
    TermList temp;
    auto res = subst.findBinding(var.var(), temp);
    if (res) {
      DEBUG("var instantiated ", var, " -> ", temp);
    }
    ASS(!res || temp != var);
    return res;
  });
}

namespace {
struct State {
  Literal* toEliminate;
  DHSet<Literal*> eliminated;
  Substitution subst;
  bool unifiedOnce = false;
};

std::ostream& operator<<(std::ostream& out, const State& state) {
  return out << *state.toEliminate << " " << state.eliminated << " " << state.subst;
}
}

Clause* FasterCondensation::simplify(Clause* cl)
{
  if (cl->length() <= 1) {
    return cl;
  }

  std::deque<State> states;
  for (const auto& lit : *cl) {
    states.push_back({ .toEliminate = lit });
  }

  while (!states.empty()) {
    auto& curr = states.front();
    DEBUG("curr ", curr);
    for (const auto& other : *cl) {
      if (curr.eliminated.contains(other) || curr.toEliminate == other) {
        continue;
      }
      Substitution subst = curr.subst;
      if (!unify(curr.toEliminate, other, subst, !curr.unifiedOnce)) {
        continue;
      }
      DEBUG("unified ", *other, " new subst ", subst);

      Literal* newToEliminate = nullptr;
      DHSet<Literal*> eliminated;
      eliminated.loadFromIterator(curr.eliminated.iter());
      eliminated.insert(curr.toEliminate);
      for (const auto& other2 : *cl) {
        if (eliminated.contains(other2)) {
          continue;
        }
        if (instantiated(other2, subst)) {
          newToEliminate = other2;
          break;
        }
      }
      if (!newToEliminate) {
        return Clause::fromIterator(cl->iterLits().filter([&](Literal* lit) {
          auto res = !eliminated.contains(lit);
          ASS(!res || !instantiated(lit, subst));
          return res;
        }), SimplifyingInference1(InferenceRule::CONDENSATION, cl));
      }
      states.push_back({
        .toEliminate = newToEliminate,
        .eliminated = std::move(eliminated),
        .subst = std::move(subst),
        .unifiedOnce = true,
      });
    }
    states.pop_front();
  }

  return cl;
}

}
