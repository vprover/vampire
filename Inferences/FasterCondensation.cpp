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
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/Backtrackable.hpp"

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

  if (base->isTwoVarEquality()) {
    if (!match(base->twoVarEqSort(), SortHelper::getEqualityArgumentSort(instance), instVars, subst)) {
      return false;
    }
  }

  for (unsigned i = 0; i < base->arity(); i++) {
    if (!match(*base->nthArgument(i), *instance->nthArgument(i), instVars, subst)) {
      return false;
    }
  }
  return true;
}

bool instantiated(const DHSet<TermList>& litVars, const Substitution& subst)
{
  DEBUG("instantiated ", *lit);
  return iterTraits(litVars.iter()).any([&subst](TermList var) {
    TermList temp;
    auto res = subst.findBinding(var.var(), temp);
    if (res) {
      DEBUG("var instantiated ", var, " -> ", temp);
    }
    ASS(!res || temp != var);
    return res;
  });
}

bool tryExtend(BacktrackData& bd, Substitution& subst, const DHSet<unsigned>& unchanged, const std::vector<DHSet<TermList>>& litVars, const Substitution& other, const DHSet<TermList>& unchanged2) {
  // in this case we would have duplicate literal removal
  ASS(!subst.isEmpty());
  ASS(!other.isEmpty());

  DEBUG("subst ", subst);
  DEBUG("other ", other);

  for (const auto& [v,t] : iterTraits(subst.items())) {
    TermList tmp;
    if (unchanged2.contains(TermList::var(v)) || (other.findBinding(v, tmp) && t != tmp)) {
      return false;
    }
  }
  for (const auto& [v,t] : iterTraits(other.items())) {
    for (const auto& i : iterTraits(unchanged.iter())) {
      if (litVars[i].contains(TermList::var(v))) {
        return false;
      }
    }
    TermList tmp;
    if (!subst.findBinding(v, tmp)) {
      ALWAYS(subst.bind(v, t));
      bd.addClosure([&subst,v](){ subst.unbind(v); });
    }
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

  std::vector<Stack<std::pair<Substitution, unsigned>>> litSubsts(cl->size());

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
      {
        Substitution subst;
        if (match(lit, other, litVars[j], subst)) {
          litSubsts[i].emplace(std::move(subst), j);
        }
      }
      if (lit->isEquality()) {
        Substitution subst2;
        if (lit->isTwoVarEquality()) {
          if (!match(lit->twoVarEqSort(), SortHelper::getEqualityArgumentSort(other), litVars[j], subst2)) {
            continue;
          }
        }
        if (match(lit->termArg(0), other->termArg(1), litVars[j], subst2) &&
            match(lit->termArg(1), other->termArg(0), litVars[j], subst2))
        {
          litSubsts[i].emplace(std::move(subst2), j);
        }
      }
    }
    DEBUG("substs for ", *lit);
    DEBUG(litSubsts[i]);
  }

  struct State {
    Substitution subst;
    DHSet<unsigned> unchanged; // indices of unchanged literals
    unsigned litI = 0;
    int substI = -1;
  };

  for (unsigned i = 0; i < cl->size(); i++) {

    for (const auto& [s,j] : litSubsts[i]) {

      DEBUG("trying with index ", i, " and subst ", s);

      // Stack<State> todo;
      // {
        DHSet<unsigned> unchanged;
        unchanged.insert(j);
        State curr(s, std::move(unchanged), 0, -1);
        // todo.emplace(s, std::move(unchanged), 0, -1);
      // }
      Stack<BacktrackData> bds;

      while (true) {
        // auto curr = todo.pop();
        if (curr.litI == i) {
          curr.litI++;
        }
        DEBUG("current state ", curr.litI, " ", curr.substI, " ", curr.subst, " ", curr.unchanged);
        // arrived at the end of clause
        if (curr.litI >= cl->size()) {
          DEBUG("finalizing");
          if (iterTraits(curr.unchanged.iter()).any([&curr,&litVars](auto i) { return instantiated(litVars[i], curr.subst); })) {
            // some earlier literal has been instantiated, fail
            INVALID_OPERATION("shouldn't happen");
          }
          auto res = Clause::fromIterator(iterTraits(curr.unchanged.iter()).map([cl](auto i) { return (*cl)[i]; }), SimplifyingInference1(InferenceRule::CONDENSATION, cl));
          if (!validateResult(cl, res, curr.subst)) {
            INVALID_OPERATION("incorrect faster condensation " + res->toString() + " from " + cl->toString());
          }
          while (bds.isNonEmpty()) {
            bds.pop().drop();
          }
          return res;
        }
        // tried everything on this literal, no more options
        if (curr.substI >= (int)litSubsts[curr.litI].size()) {
          DEBUG("fail");
          if (bds.isNonEmpty()) {
            auto bd = bds.pop();
            bd.backtrack();
            continue;
          }
          break;
        }
        BacktrackData bd;
        auto currLitI = curr.litI;
        auto currSubstI = curr.substI;
        bd.addClosure([&curr,currLitI,currSubstI](){ curr.litI = currLitI; curr.substI = currSubstI + 1; });

        // one option is to try the next substitution
        DHSet<unsigned> unchanged;
        unchanged.loadFromIterator(curr.unchanged.iter());
        // todo.emplace(curr.subst, std::move(unchanged), curr.litI, curr.substI+1);
        // the other option is to move to the next literal
        if (curr.substI == -1) {
          if (!instantiated(litVars[curr.litI], curr.subst)) {
            DEBUG("unchanged ", (*cl)[curr.litI]);
            if (curr.unchanged.insert(curr.litI)) {
              bd.addClosure([&curr,currLitI](){ curr.unchanged.remove(currLitI); });
            }
            curr.litI++;
            curr.substI = -1;
            // todo.push(std::move(curr));
            bds.push(std::move(bd));
            continue;
          }
        } else if (tryExtend(bd, curr.subst, curr.unchanged, litVars, litSubsts[curr.litI][curr.substI].first, litVars[litSubsts[curr.litI][curr.substI].second])) {
          DEBUG("subst extended");
          auto v = litSubsts[curr.litI][curr.substI].second;
          if (curr.unchanged.insert(v)) {
            bd.addClosure([&curr,v](){ curr.unchanged.remove(v); });
          }
          curr.litI++;
          curr.substI = -1;
          // todo.push(std::move(curr));
          bds.push(std::move(bd));
          continue;
        }
        bd.backtrack();
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
