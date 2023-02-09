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
 * @file LazyIndex.cpp
 * Lazy term indexing
 */

#include "LazyIndex.hpp"
#include "Kernel/RobSubstitution.hpp"

namespace Indexing {

unsigned Positions::child(unsigned parent, unsigned argument) {
  CALL("Positions::child");
  Entry &entry = _entries[parent];
  while(entry.children.size() <= argument) {
    unsigned child = _entries.size();
    unsigned argument = entry.children.size();
    _entries.push(Entry(parent, argument));
    entry.children.push(child);
  }
  return entry.children[argument];
}

static Stack<unsigned> arguments;

TermList Positions::term_at(TermList term, unsigned position) {
  CALL("Positions::term_at")

  arguments.reset();
  while(position) {
    arguments.push(_entries[position].argument);
    position = _entries[position].parent;
  }

  while(arguments.isNonEmpty()) {
    if(term.isVar())
      return term;

    Term *compound = term.term();
    unsigned argument = arguments.pop();
    if(compound->arity() <= argument) {
      term.makeEmpty();
      return term;
    }

    term = (*compound)[argument];
  }

  return term;
}

struct Unify {
  TermList query;
  TermList candidate;
  unsigned position;
};

static Stack<Unify> unify;

LazyIndex::Reason LazyIndex::explain(TermList query, TermList candidate) {
  CALL("LazyIndex::explain")

  unify.reset();
  unify.push({.query = query, .candidate = candidate, .position = 0});

  while(unify.isNonEmpty()) {
    Unify next = unify.pop();
    if(next.query.isVar() || next.candidate.isVar())
      continue;

    Term *query = next.query.term();
    Term *candidate = next.candidate.term();
    unsigned position = next.position;
    if(query->functor() != candidate->functor()) {
      mismatch_position = position;
      mismatch_candidate_functor = candidate->functor();
      return Reason::MISMATCH;
    }

    for(unsigned i = 0; i < query->arity(); i++) {
      unsigned argument_position = _positions.child(position, i);
      unify.push({
        .query = (*query)[i],
        .candidate = (*candidate)[i],
        .position = argument_position
      });
    }
  }

  return Reason::NO_REASON;
}

DHMap<unsigned, LazyIndex::Branch> LazyIndex::QueryIterator::EMPTY_BRANCH_MAP;

bool LazyIndex::QueryIterator::hasNext() {
  CALL("LazyIndex::hasNext")

  while(_todo.isNonEmpty()) {
new_branch:
    Iteration &iteration = _todo.top();

    while(iteration.immediate.hasNext()) {
      TermList candidate = iteration.immediate.next();

      RobSubstitution &substitution = *_index._substitution;
      substitution.reset();
      if(substitution.unify(_query, 0, candidate, 1)) {
        _next = candidate;
        return true;
      }

      Reason reason = _index.explain(_query, candidate);
      switch(reason) {
        case Reason::NO_REASON:
          continue;
        case Reason::MISMATCH:
        {
          iteration.immediate.del();
          FunctorAt *functor_at;
          iteration.branch.positions.getValuePtr(_index.mismatch_position, functor_at);
          // iterator might be invalidated by new entry
          ::new(&iteration.functors) decltype(iteration.functors)(iteration.branch.positions);

          Branch *child;
          functor_at->functors.getValuePtr(_index.mismatch_candidate_functor, child);
          child->immediate.push(candidate);
        }
      }
    }

new_branches:
    if(iteration.branches.hasNext()) {
      unsigned functor;
      Branch &branch = iteration.branches.nextRef(functor);
      _todo.push(Iteration(branch));
      goto new_branch;
    }

    if(iteration.functors.hasNext()) {
      unsigned position;
      FunctorAt &functor_at = iteration.functors.nextRef(position);
      TermList subterm = _index._positions.term_at(_query, position);
      if(subterm.isVar()) {
        ::new(&iteration.branches) decltype(iteration.branches)(functor_at.functors);
        goto new_branches;
      }
      else if(subterm.isTerm()) {
        Term *compound = subterm.term();
        Branch *child = functor_at.functors.findPtr(compound->functor());
        if(child) {
          _todo.push(Iteration(*child));
          goto new_branch;
        }
      }
    }

    _todo.pop();
  }

  return false;
}

void LazyTermIndex::insert(TermList t, Literal* lit, Clause* cls) {
  CALL("LazyTermIndex::insert(TermList, Literal *, Clause *)")
  Stack<Entry> *entry;
  if(_entries.getValuePtr(t, entry))
    _index.insert(t);

  entry->push({
    .literal = lit,
    .clause = cls
  });
}

void LazyTermIndex::remove(TermList t, Literal *lit, Clause *cls) {
  CALL("LazyTermIndex::remove")
  Stack<Entry> &entries = _entries.get(t);
  for(unsigned i = 0; i < entries.size(); i++)
    // TODO check if entry is empty and remove from _index
    if(entries[i].literal == lit && entries[i].clause == cls) {
      std::swap(entries[i--], entries[entries.size() - 1]);
      entries.pop();
      return;
    }
}

TermQueryResultIterator LazyTermIndex::getUnifications(TermList query, bool retrieveSubstitutions) {
  CALL("LazyTermIndex::getUnifications(TermList, bool)")

  return pvi(getMapAndFlattenIterator(
    LazyIndex::QueryIterator(_index, query),
    [this](TermList result) {
      return pvi(getMappingIterator(
        _entries.get(result).iter(),
        [this, result](Entry entry) {
          return TermQueryResult(result, entry.literal, entry.clause, _index.substitution);
        }
      ));
  }));
}

} //namespace Indexing
