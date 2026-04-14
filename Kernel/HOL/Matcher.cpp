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
 * @file Matcher.cpp
 * Implements class HOL::Matcher.
 */

#include "HOL.hpp"
#include "Kernel/Matcher.hpp"

#include "Matcher.hpp"

namespace Kernel::HOL {

// lam: >[X0,X1] : X1 -> (X0 -> X1)
// app: >[X0,X1] : (X0 -> X1) -> X0 -> X1

bool Matcher::hasNext()
{
  while (todo.isNonEmpty())
  {
    auto [base, instance] = todo.pop();

    DBG("matching ", base, " onto ", instance);

    ::HOL::normaliseLambdaPrefixes(base, instance);

    DBG("normalized ", base, " and ", instance);

    if (base.isVar()) {
      if (instance.containsLooseDBIndex()) {
        return false; // TODO backtrack
      }
      continue;
    }
    if (!instance.isTerm()) {
      return false; // TODO backtrack
    }

    auto baseM = base;
    auto instM = instance;
    while (baseM.isLambdaTerm()) {
      ASS(instM.isLambdaTerm());
      auto bt = baseM.term();
      auto it = instM.term();

      // match types in the normal way
      if (!MatchingUtils::matchTerms(bt->typeArg(0), it->typeArg(0), subst) ||
          !MatchingUtils::matchTerms(bt->typeArg(1), it->typeArg(1), subst))
      {
        DBG("type args don't match");
        return false; // TODO backtrack
      }

      instM = TypedTermList(it->termArg(0), it->typeArg(1));
      baseM = TypedTermList(bt->termArg(0), bt->typeArg(1));
    }

    DBG("matrices ", baseM, " ", instM);

    auto baseH = baseM;
    Stack<TypedTermList> baseArgs;
    while (baseH.isApplication()) {
      auto bt = baseH.term();
      baseArgs.emplace(bt->typeArg(0), AtomicSort::superSort());
      baseArgs.emplace(bt->typeArg(1), AtomicSort::superSort());
      baseArgs.emplace(bt->termArg(1), bt->typeArg(1));
      baseH = TypedTermList(bt->termArg(0), bt->typeArg(0));
    }

    auto instH = instM;
    Stack<TypedTermList> instArgs;
    while (instH.isApplication()) {
      auto iht = instH.term();
      instArgs.emplace(iht->typeArg(0), AtomicSort::superSort());
      instArgs.emplace(iht->typeArg(1), AtomicSort::superSort());
      instArgs.emplace(iht->termArg(1), iht->typeArg(0));
      instH = TypedTermList(iht->termArg(0), iht->typeArg(0));
    }

    DBG("heads ", baseH, " ", instH);

    if (instH.isLambdaTerm()) {
      INVALID_OPERATION("instance " + instance.toString() + " is not in beta-eta normal form");
    }

    if (baseH.isTerm()) {
      if (instH.isVar()) {
        return false; // TODO backtrack
      }

      auto bht = baseH.term();
      auto iht = instH.term();
      if (bht->functor() != iht->functor()) {
        return false; // TODO backtrack
      }

      ASS_EQ(baseArgs.size(), instArgs.size());
      for (unsigned i = 0; i < baseArgs.size(); i++) {
        if (baseArgs[i].sort() == AtomicSort::superSort()) {
          ASS_EQ(instArgs[i].sort(), AtomicSort::superSort());
          if (!MatchingUtils::matchTerms(baseArgs[i], instArgs[i], subst)) {
            return false; // TODO backtrack
          }
        } else {
          ASS_NEQ(instArgs[i].sort(), AtomicSort::superSort());
          todo.emplace(baseArgs[i], instArgs[i]);
        }
      }
      continue;
    }

    auto varSort = baseH.sort();
    TermStack sorts;
    while (varSort.isArrowSort()) {
      sorts.push(varSort.domain());
      varSort = varSort.result();
    }
    sorts.push(varSort);

    // surround instance matrix in lambdas
    auto t = ::HOL::create::surroundWithLambdas(instM, sorts);
    DBG("try bind ", baseH.var(), " -> ", t);

    if (!subst.bind(baseH.var(), t)) {
      return false; // TODO backtrack
    }
  }
  return true;
}

bool Matcher::matches(TypedTermList base, TypedTermList instance)
{
  DBG("Matcher::matches");
  Matcher matcher(base, instance);
  return matcher.hasNext();
}

}