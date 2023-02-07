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

namespace Indexing {

void LazyIndex::insert(TermList t) {
  CALL("LazyIndex::insert")
  std::cout << "insert: " << t.toString() << std::endl;
  _root.terms.push(t);
}

bool LazyIndex::Iterator::hasNext() {
  while(_positions.isNonEmpty()) {
    Position &position = _positions.top();
    if(position.index == position.node.terms.size()) {
      _positions.pop();
      continue;
    }

    TermList t = position.node.terms[position.index++];
    std::cout << "candidate: " << t.toString() << std::endl;

    _substitution.reset();
    if(_substitution.unify(_query, 0, t, 1)) {
      std::cout << "OK" << std::endl;
      _next = t;
      return true;
    }
  }

  return false;
}

void LazyTermIndex::insert(TermList t, Literal* lit, Clause* cls) {
  CALL("LazyTermIndex::insert(TermList, Literal *, Clause *)")
  Stack<Entry> empty, *entry;
  if(_entries.getValuePtr(t, entry, empty))
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
    LazyIndex::Iterator(_index, query),
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
