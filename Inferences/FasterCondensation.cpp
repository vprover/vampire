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
#include "Kernel/Matcher.hpp"
#include "Kernel/SubstHelper.hpp"
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

bool match(TermList base, TermList instance, const DHSet<TermList>& instVars, Substitution& subst)
{
  Recycled<Stack<std::pair<TermList, TermList>>> todo;
  todo->emplace(base, instance);

  while (todo->isNonEmpty()) {
    auto [b, i] = todo->pop();

    if (b.weight() > i.weight()) {
      return false;
    }
    if (b == i) {
      continue;
    }
    if (b.isVar()) {
      if (instVars.contains(b) || !subst.bind(b.var(), i)) {
        return false;
      }
      continue;
    }
    if (i.isVar() || b.term()->functor() != i.term()->functor()) {
      return false;
    }
    todo->loadFromIterator(anyArgIter(b.term()).zip(anyArgIter(i.term())));
  }
  return true;
}

bool match(Literal* base, Literal* instance, const DHSet<TermList>& instVars, Substitution& subst)
{
  ASS(Literal::headersMatch(base, instance, /*complementary=*/false));
  for (unsigned i = 0; i < base->arity(); i++) {
    if (!match(*base->nthArgument(i), *instance->nthArgument(i), instVars, subst)) {
      return false;
    }
  }
  return true;
}

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

// Clause* FasterCondensation::simplify(Clause* cl)
// {
//   if (cl->length() <= 1) {
//     return cl;
//   }

//   std::deque<State> states;
//   for (const auto& lit : *cl) {
//     states.push_back({ .toEliminate = lit });
//   }

//   while (!states.empty()) {
//     auto& curr = states.front();
//     DEBUG("curr ", curr);
//     for (const auto& other : *cl) {
//       if (curr.eliminated.contains(other) || curr.toEliminate == other) {
//         continue;
//       }
//       Substitution subst = curr.subst;
//       if (!unify(curr.toEliminate, other, subst, !curr.unifiedOnce)) {
//         continue;
//       }
//       DEBUG("unified ", *other, " new subst ", subst);

//       Literal* newToEliminate = nullptr;
//       DHSet<Literal*> eliminated;
//       eliminated.loadFromIterator(curr.eliminated.iter());
//       eliminated.insert(curr.toEliminate);
//       for (const auto& other2 : *cl) {
//         if (eliminated.contains(other2)) {
//           continue;
//         }
//         if (instantiated(other2, subst)) {
//           newToEliminate = other2;
//           break;
//         }
//       }
//       if (!newToEliminate) {
//         return Clause::fromIterator(cl->iterLits().filter([&](Literal* lit) {
//           auto res = !eliminated.contains(lit);
//           ASS(!res || !instantiated(lit, subst));
//           return res;
//         }), SimplifyingInference1(InferenceRule::CONDENSATION, cl));
//       }
//       states.push_back({
//         .toEliminate = newToEliminate,
//         .eliminated = std::move(eliminated),
//         .subst = std::move(subst),
//         .unifiedOnce = true,
//       });
//     }
//     states.pop_front();
//   }

//   return cl;
// }

DHSet<TermList> getForbiddenVars(const Substitution& subst)
{
  DHSet<TermList> res;
  res.loadFromIterator(iterTraits(subst.items())
    .flatMap([](auto arg) { return VariableIterator(arg.second); }));
  return res;
}

bool tryExtend(Substitution& subst, const Substitution& other) {
  // in this case we would have duplicate literal removal
  ASS(!subst.isEmpty());
  ASS(!other.isEmpty());

  DEBUG("subst ", subst);
  DEBUG("other ", other);

  auto forbidden1 = getForbiddenVars(subst);
  auto forbidden2 = getForbiddenVars(other);

  for (const auto& [v,t] : iterTraits(subst.items())) {
    TermList tmp;
    if (forbidden2.contains(TermList::var(v)) || (other.findBinding(v, tmp) && t != tmp)) {
      return false;
    }
  }
  for (const auto& [v,t] : iterTraits(other.items())) {
    if (forbidden1.contains(TermList::var(v))) {
      return false;
    }
    ALWAYS(subst.bind(v, t));
  }
  return true;
}

bool validateResult(Clause*, Clause*, const Substitution&);

Clause* FasterCondensation::simplify(Clause* cl)
{
  if (cl->length() <= 1) {
    return cl;
  }

  DEBUG("cl ", *cl);

  std::vector<DHSet<TermList>> litVars(cl->size());
  for (unsigned i = 0; i < cl->size(); i++) {
    auto lit = (*cl)[i];
    litVars[i].loadFromIterator(VariableIterator(lit));
  }

  std::vector<Stack<Substitution>> litSubsts(cl->size());

  for (unsigned i = 0; i < cl->size(); i++) {
    auto lit = (*cl)[i];
    // if (lit->isEquality() && lit->isNegative()) {
    // TODO do equality resolution part too
    // }
    for (unsigned j = 0; j < cl->size(); j++) {
      auto other = (*cl)[j];
      if (lit == other || !Literal::headersMatch(lit, other, /*complementary=*/false)) {
        continue;
      }
      Substitution subst;

      if (match(lit, other, litVars[j], subst)) {
        litSubsts[i].push(std::move(subst));
      }
      if (lit->isEquality()) {
        Substitution subst2;
        if (match(lit->termArg(0), other->termArg(1), litVars[j], subst2) &&
            match(lit->termArg(1), other->termArg(0), litVars[j], subst2))
        {
          litSubsts[i].push(std::move(subst2));
        }
      }
    }
    DEBUG("substs for ", *lit);
    DEBUG(litSubsts[i]);
  }

  struct State {
    Substitution subst;
    LiteralStack unchanged;
    unsigned litI = 0;
    int substI = -1;
  };

  for (unsigned i = 0; i < cl->size(); i++) {

    for (const auto& s : litSubsts[i]) {

      DEBUG("trying with index ", i, " and subst ", s);

      Stack<State> todo;
      todo.emplace(s, LiteralStack(), 0, -1);

      while (todo.isNonEmpty()) {
        auto curr = todo.pop();
        if (curr.litI == i) {
          curr.litI++;
        }
        DEBUG("current state ", curr.litI, " ", curr.substI, " ", curr.subst, " ", curr.unchanged);
        // arrived at the end of clause
        if (curr.litI >= cl->size()) {
          DEBUG("finalizing");
          if (iterTraits(curr.unchanged.iter()).any([&curr](auto l) { return instantiated(l, curr.subst); })) {
            // some earlier literal has been instantiated, fail
            continue;
          }
          auto res = Clause::fromIterator(curr.unchanged.iter(), SimplifyingInference1(InferenceRule::CONDENSATION, cl));
          if (!validateResult(cl, res, curr.subst)) {
            INVALID_OPERATION("incorrect faster condensation " + res->toString() + " from " + cl->toString());
          }
          return res;
        }
        // tried everything on this literal, no more options
        if (curr.substI >= (int)litSubsts[curr.litI].size()) {
          DEBUG("fail");
          continue;
        }
        // one option is to try the next substitution
        todo.emplace(curr.subst, curr.unchanged, curr.litI, curr.substI+1);
        // the other option is to move to the next literal
        if (curr.substI == -1) {
          if (!instantiated((*cl)[curr.litI], curr.subst)) {
            DEBUG("unchanged ", (*cl)[curr.litI]);
            curr.unchanged.push((*cl)[curr.litI]);
            curr.litI++;
            curr.substI = -1;
            todo.push(std::move(curr));
          }
        } else if (tryExtend(curr.subst, litSubsts[curr.litI][curr.substI])) {
          DEBUG("subst extended");
          curr.litI++;
          curr.substI = -1;
          todo.push(std::move(curr));
        }
      }
    }
  }

  return cl;
}

bool validateResult(Clause* premise, Clause* conclusion, const Substitution& subst)
{
  DHSet<unsigned> unbound;
  unbound.loadFromIterator(iterTraits(subst.items())
    .map([](auto arg) { return arg.second; })
    .flatMap([](auto t) { return iterTraits(VariableIterator(t)); })
    .map([](auto v) { return v.var(); }));

  if (iterTraits(subst.items()).any([&](auto arg) { return unbound.contains(arg.first); })) {
    DEBUG("substitution is not idempotent ", subst);
    return false;
  }

  DHSet<Literal*> resLits;
  resLits.loadFromIterator(conclusion->iterLits());

  for (const auto& lit : *premise) {
    auto litS = SubstHelper::apply(lit, subst);
    if (!resLits.contains(litS)) {
      DEBUG("result does not contain ", *litS);
      return false;
    }
  }

  return true;
}

}
