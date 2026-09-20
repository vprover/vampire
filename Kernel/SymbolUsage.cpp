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
#include "Kernel/TermIterators.hpp"

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

void SymbolCounts::countIn(ClauseIterator clauses)
{
  functions.init(env.signature->functions(),0);
  predicates.init(env.signature->predicates(),0);
  typeCons.init(env.signature->typeCons(),0);
  _initialised = true;

  while (clauses.hasNext()) {
    Clause* cl = clauses.next();
    for (unsigned i = 0; i < cl->length(); i++) {
      Literal* lit = (*cl)[i];
      ASS(lit->shared());
      // equality is not counted: it is the one predicate every consumer of these numbers
      // wants to ignore, and Property::scan left it out too
      if (!lit->isEquality()) {
        predicates[lit->functor()]++;
      }
      // deliberately no visited set here, see the header. SubtermIterator walks the type
      // arguments along with the rest, so the sorts inside a literal are reached as well
      SubtermIterator stit(lit);
      while (stit.hasNext()) {
        TermList ts = stit.next();
        if (!ts.isTerm()) {
          continue;
        }
        Term* t = ts.term();
        // SubtermIterator only follows args(), so it would silently skip whatever hides
        // in the special data of a special term. Clause literals must not contain one:
        // a term with a special subterm cannot be shared.
        ASS(!t->isSpecial());
        if (t->isSort()) {
          // an AtomicSort stores the type constructor's number as its functor
          typeCons[t->functor()]++;
        }
        else {
          functions[t->functor()]++;
        }
      }
    }
  }
}

}
