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
 * @file SATIndex.cpp
 * Term indices based on an internal SAT solver
 */

#include "SATIndex.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Indexing/ResultSubstitution.hpp"

namespace Indexing {

SATIndex::SATIndex() {
  CALL("SATIndex")
  _substitution = new RobSubstitution;
  _lastLink = freshLiteral();
  _solver.addClause(_lastLink);
  substitution = ResultSubstitution::fromSubstitution(_substitution, 0, 1);
}

SATIndex::~SATIndex() {
  CALL("~SATIndex")
  delete _substitution;
}

void SATIndex::insert(TermList term) {
  CALL("SATIndex::insert")
  std::cout << "insert: " << term.toString() << std::endl;

  // get a new variable for a term
  Minisat::Lit termLiteral = freshTermLiteral(term);

  // "link" it into the giant clause of indexed terms
  Minisat::Lit previousLink = _lastLink;
  _lastLink = freshLiteral();
  _solver.addClause(~previousLink, termLiteral, _lastLink);
}

void SATIndex::prepareUnifications(TermList query) {
  CALL("SATIndex::prepareUnifications")
  std::cout << "unifications: " << query.toString() << std::endl;

  _query = query;
  _assumptions.clear();
  _assumptions.push(~_lastLink);
  _next = _terms.size();
}

TermList SATIndex::next() {
  CALL("SATIndex::next")

  do {
    for(; _next < _terms.size(); _next++) {
      if(_terms[_next].isEmpty() || _solver.modelValue(_next) == Minisat::l_False)
        continue;

      TermList candidate = _terms[_next];
      std::cout << "candidate: " << candidate.toString() << std::endl;
      _assumptions.push(~Minisat::mkLit(_next));

      _substitution->reset();
      if(_substitution->unify(_query, 0, candidate, 1)) {
        std::cout << "success: " << _substitution->toString() << std::endl;
        _next++;
        return candidate;
      }
    }
    _next = 0;
  } while(_solver.solve(_assumptions));

  std::cout << "done" << std::endl;
  TermList empty;
  empty.makeEmpty();
  return empty;
}

Minisat::Lit SATIndex::freshLiteral() {
  CALL("SATIndex::freshLiteral")
  TermList empty;
  empty.makeEmpty();
  _terms.push(empty);
  return Minisat::mkLit(_solver.newVar());
}

Minisat::Lit SATIndex::freshTermLiteral(TermList term) {
  CALL("SATIndex::termLiteral")
  ASS(term.isNonEmpty())
  auto literal = Minisat::mkLit(_solver.newVar());
  _terms.push(term);
  return literal;
}

void SATTermIndex::insert(TermList term, Literal *literal, Clause* clause) {
  CALL("SATTermIndex::insert(TermList, Literal *, Clause *)")
  Stack<Entry> empty, *entry;
  if(_entries.getValuePtr(term, entry, empty))
    _index.insert(term);
  entry->push({literal, clause});
}

void SATTermIndex::remove(TermList term, Literal *literal, Clause *clause) {
  CALL("SATTermIndex::remove")
  Stack<Entry> &entries = _entries.get(term);
  for(unsigned i = 0; i < entries.size(); i++)
    if(entries[i].literal == literal && entries[i].clause == clause) {
      std::swap(entries[i--], entries[entries.size() - 1]);
      entries.pop();
      return;
    }
}

TermQueryResultIterator SATTermIndex::getUnifications(TermList query, bool retrieveSubstitutions) {
  return pvi(getMapAndFlattenIterator(
    SATIndex::Unifications(_index, query),
    [this](TermList result) {
      return pvi(getMappingIterator(
        _entries.get(result).iter(),
        [this, result](Entry entry) {
          return TermQueryResult(result, entry.literal, entry.clause, _index.substitution);
        }
      ));
  }));
}
} // namespace Indexing
