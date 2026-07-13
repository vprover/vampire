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

/**
 * A literal without any substitutions stays in the clause since there is no way to instantiate it
 * to make it a duplicate literal. All variables of such clauses become 'uninstantiable', and we
 * can remove all substitutions binding them (assuming they are not bound to themselves). We perform
 * the fixpoint of finding such uninstantiable variables and removing substitutions.
 */
void removeUninstantiable(std::vector<Stack<std::pair<Substitution, unsigned>>>& litSubsts, const std::vector<DHSet<TermList>>& litVars)
{
  DHSet<TermList> uninstantiable;
  bool added = false;

  auto loadUninstantiable = [&](unsigned i) {
    if (litSubsts[i].isEmpty()) {
      for (const auto& var : iterTraits(litVars[i].iter())) {
        added = added || uninstantiable.insert(var);
      }
    }
  };

  for (unsigned i = 0; i < litSubsts.size(); i++) {
    loadUninstantiable(i);
  }

  while (added) {
    added = false;
    for (unsigned i = 0; i < litSubsts.size(); i++) {
      for (unsigned j = 0; j < litSubsts[i].size();) {
        auto& subst = litSubsts[i][j].first;
        if (iterTraits(uninstantiable.iter()).any([&subst](auto var) {
          TermList temp;
          return subst.findBinding(var.var(), temp);
        })) {
          litSubsts[i].swapRemove(j);
          continue;
        }
        j++;
      }
      loadUninstantiable(i);
    }
  }
}

struct State {
  State(Substitution subst, unsigned initial) : subst(subst) {
    unchanged.insert(initial);
  }

  Substitution subst;
  DHSet<unsigned> unchanged; // indices of unchanged literals
  unsigned litI = 0;
  int substI = -1;
};

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

  removeUninstantiable(litSubsts, litVars);

  for (unsigned i = 0; i < cl->size(); i++) {

    for (const auto& [s,j] : litSubsts[i]) {

      DEBUG("trying with index ", i, " and subst ", s);

      State state(s, j);
      static Stack<BacktrackData> bds;
      ASS(bds.isEmpty());

      for (;;) {
        if (state.litI == i) {
          state.litI++;
        }
        DEBUG("current state ", curr.litI, " ", curr.substI, " ", curr.subst, " ", curr.unchanged);
        // arrived at the end of clause
        if (state.litI >= cl->size()) {
          DEBUG("finalizing");
          // if (iterTraits(state.unchanged.iter()).any([&state,&litVars](auto i) { return instantiated(litVars[i], state.subst); })) {
          //   // some earlier literal has been instantiated, fail
          //   INVALID_OPERATION("shouldn't happen");
          // }
          auto res = Clause::fromIterator(iterTraits(state.unchanged.iter()).map([cl](auto i) { return (*cl)[i]; }), SimplifyingInference1(InferenceRule::CONDENSATION, cl));
          // if (!validateResult(cl, res, state.subst)) {
          //   INVALID_OPERATION("incorrect faster condensation " + res->toString() + " from " + cl->toString());
          // }
          while (bds.isNonEmpty()) {
            bds.pop().drop();
          }
          return res;
        }
        // tried everything on this literal, no more options
        if (state.substI >= (int)litSubsts[state.litI].size()) {
          DEBUG("fail");
          if (bds.isNonEmpty()) {
            auto bd = bds.pop();
            bd.backtrack();
            continue;
          }
          break;
        }
        // one option is to try the next substitution, this is captured by the backtrack data below
        BacktrackData bd;
        auto currLitI = state.litI;
        auto currSubstI = state.substI;
        bd.addClosure([&state,currLitI,currSubstI](){ state.litI = currLitI; state.substI = currSubstI + 1; });

        // the other option is to move to the next literal
        if (state.substI == -1) {
          if (!instantiated(litVars[state.litI], state.subst)) {
            DEBUG("unchanged ", (*cl)[curr.litI]);
            if (state.unchanged.insert(state.litI)) {
              bd.addClosure([&state,currLitI](){ state.unchanged.remove(currLitI); });
            }
            state.litI++;
            state.substI = -1;
            bds.push(std::move(bd));
            continue;
          }
        } else if (tryExtend(bd, state.subst, state.unchanged, litVars, litSubsts[state.litI][state.substI].first, litVars[litSubsts[state.litI][state.substI].second])) {
          DEBUG("subst extended");
          auto v = litSubsts[state.litI][state.substI].second;
          if (state.unchanged.insert(v)) {
            bd.addClosure([&state,v](){ state.unchanged.remove(v); });
          }
          state.litI++;
          state.substI = -1;
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
