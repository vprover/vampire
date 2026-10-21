/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "ArgPruning.hpp"

#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

namespace Inferences {

void appArgs(TermList t, TermStack& args) {
  if (t.isApplication()) {
    appArgs(t.lhs(), args);
    args.push(t.rhs());
  }
}

std::pair<TermList,TermList> discardIndices(TermList t, TermList sort, DHSet<unsigned, FnvHash, IdentityHash>& discardedIndices, unsigned index) {
  if (t.isApplication()) {
    auto isDiscarded = discardedIndices.contains(index);
    auto [lhs, lhsSort] = discardIndices( t.lhs(), isDiscarded ? sort : AtomicSort::arrowSort(t.term()->typeArg(0), sort), discardedIndices, index-1);
    if (isDiscarded) {
      return { lhs, lhsSort };
    }
    return { HOL::create::app(lhsSort, lhs, t.rhs()), lhsSort.result() };
  }
  return { t, sort };
}

bool isIndexDiscardable(const TermStack& ts, unsigned index, const DHSet<unsigned, FnvHash, IdentityHash>& discardedIndices, unsigned freshVar)
{
  DHSet<TermList, TermListHash, TermListHash2> termSet;
  for (const auto& t : ts) {
    TermStack args;
    appArgs(t, args);
    auto terms = BottomUpEvaluation<TermList, TermStack>()
      .function([&](TermList t, TermStack* children) {
          TermStack res;
          // there are all the other arguments directly imitating the term
          for (unsigned i = 0; i < args.size(); i++) {
            if (i == index || discardedIndices.contains(i)) { continue; }
            if (args[i] == t) { res.push(TermList::var(freshVar+i)); }
          }

          if (t.isVar()) {
            res.push(t);
          } else {
            auto tt = t.term();
            Stack<TermStack> argStacks;
            argStacks.emplace();
            for (unsigned i = 0; i < tt->numTypeArguments(); i++) {
              argStacks.top().push(tt->typeArg(i));
            }
            for (unsigned i = 0; i < tt->numTermArguments(); i++) {
              Stack<TermStack> newArgStacks;
              for (const auto& st : argStacks) {
                for (const auto& s : children[i]) {
                  newArgStacks.push(st);
                  newArgStacks.top().push(s);
                }
              }
              std::swap(argStacks,newArgStacks);
            }
            for (const auto& targs : argStacks) {
              res.emplace(Term::create(tt->functor(), targs));
            }
          }
          return res;
      })
      .apply(args[index]);

    ASS(terms.isNonEmpty());

    if (termSet.isEmpty()) {
      termSet.loadFromIterator(terms.iter());
    } else {
      decltype(termSet)::DelIterator dit(termSet);
      while (dit.hasNext()) {
        auto e = dit.next();
        if (!terms.find(e)) {
          dit.del();
        }
      }
      if (termSet.isEmpty()) {
        return false;
      }
    }
  }
  ASS(!termSet.isEmpty());
  return true;
}

// algorithm is based on PruneArg in https://matryoshka-project.github.io/pubs/bentkamp_phd_thesis.pdf
Clause* ArgPruning::simplify(Clause* c)
{
  DHMap<unsigned, TermStack, FnvHash, IdentityHash> varOccurrences;
  unsigned freshVar = c->maxVar()+1;

  for (const auto& l : *c) {
    SubtermIterator sti(l);
    while (sti.hasNext()) {
      auto st = sti.next();
      if (st.isTerm() && !st.isApplication()) {
        continue;
      }
      auto head = st.head();
      if (head.isTerm()) {
        continue;
      }

      TermStack* ptr;
      varOccurrences.getValuePtr(head.var(), ptr);
      ptr->push(st);
      sti.right();
    }
  }

  bool modified = false;
  auto resLits = LiteralStack::fromIterator(c->iterLits());

  decltype(varOccurrences)::Iterator it(varOccurrences);
  while (it.hasNext()) {
    unsigned v;
    auto& ts = it.nextRef(v);
    ASS(ts.isNonEmpty());

    // get the minimum arity of all applications
    Stack<unsigned> arities;
    for (auto t : ts) {
      unsigned arity = 0;
      while (t.isApplication()) {
        t = t.lhs();
        arity++;
      }
      arities.push(arity);
    }
    auto minArity = iterTraits(arities.iter()).min().unwrap();
    if (minArity == 0) {
      continue;
    }
    // truncate terms to minimum arity, the rest are not needed
    for (unsigned i = 0; i < ts.size(); i++) {
      auto arity = arities[i];
      while (arity > minArity) {
        ts[i] = ts[i].lhs();
        arity--;
      }
    }

    DHSet<unsigned, FnvHash, IdentityHash> discardedIndices;

    for (unsigned i = 0; i < minArity; i++) {
      if (isIndexDiscardable(ts, i, discardedIndices, freshVar)) {
        discardedIndices.insert(i);
      }
    }

    if (discardedIndices.isEmpty()) {
      continue;
    }

    modified = true;
    for (const auto& t : ts) {
      auto [d,s] = discardIndices( t, SortHelper::getResultSort(t.term()), discardedIndices, minArity-1);
      for (auto& l : resLits) {
        l = EqHelper::replace(l, t, d);
      }
    }
  }

  if (modified) {
    return Clause::fromStack(resLits, SimplifyingInference1(InferenceRule::ARG_PRUNING, c));
  }

  return c;
}

}
