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
 * @file SymbolUsage.cpp
 * Implements the symbol usage queries declared in SymbolUsage.hpp.
 */

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "SymbolUsage.hpp"

namespace Kernel {

/**
 * The callers ask about the signature as it is now, so that is what the arrays are sized
 * to. A caller that keeps them while introducing further symbols must treat an index past
 * the end as "not used" -- which is the truthful answer, a symbol that did not exist when
 * these clauses were walked cannot occur in them.
 */
void collectUsedSymbols(ClauseIterator clauses, DArray<bool>& usedFunctions, DArray<bool>& usedPredicates)
{
  usedFunctions.init(env.signature->functions(),false);
  usedPredicates.init(env.signature->predicates(),false);

  DHSet<Term*, SharedTermHash, PtrIdentityHash> seen;
  Stack<Term*> todo;

  while (clauses.hasNext()) {
    Clause* cl = clauses.next();
    for (unsigned i = 0; i < cl->length(); i++) {
      Literal* lit = (*cl)[i];
      ASS(lit->shared()); // so the ids the visited set hashes by are meaningful
      usedPredicates[lit->functor()] = true;
      for (TermList* ts = lit->args(); ts->isNonEmpty(); ts = ts->next()) {
        if (ts->isTerm()) {
          todo.push(ts->term());
        }
      }
      while (todo.isNonEmpty()) {
        Term* t = todo.pop();
        ASS(t->shared());
        // a sort is built from type constructors, not from function symbols, and so are
        // all of its arguments, so the whole subtree is of no interest here
        if (t->isSort() || !seen.insert(t)) {
          continue;
        }
        usedFunctions[t->functor()] = true;
        for (TermList* ts = t->args(); ts->isNonEmpty(); ts = ts->next()) {
          if (ts->isTerm()) {
            todo.push(ts->term());
          }
        }
      }
    }
  }
}

}
