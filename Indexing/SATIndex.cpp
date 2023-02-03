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

  // get a new variable for a term
  Minisat::Lit termLiteral = freshTermLiteral(term);

  // "link" it into the giant clause of indexed terms
  Minisat::Lit previousLink = _lastLink;
  _lastLink = freshLiteral();
  _solver.addClause(~previousLink, termLiteral, _lastLink);
}

void SATIndex::prepareUnifications(TermList query) {
  CALL("SATIndex::prepareUnifications")

  _query = query;
  _assumptions.clear();
  _assumptions.push(~_lastLink);
  _next = _terms.size();

  Stack<std::pair<TermList, unsigned>> todo;
  todo.push({query, 0});
  while(todo.isNonEmpty()) {
    auto next = todo.pop();
    if(next.first.isVar())
      continue;
    Term *term = next.first.term();
    _assumptions.push(symbolOccursAt(term->functor(), next.second));

    for(unsigned i = 0; i < term->arity(); i++)
      todo.push({(*term)[i], position(next.second, i)});
  }
}

TermList SATIndex::next() {
  CALL("SATIndex::next")

  TermList empty;
  empty.makeEmpty();
  while(true) {
    for(; _next < _terms.size(); _next++) {
      if(_terms[_next].isEmpty() || _solver.modelValue(_next) == Minisat::l_False)
        continue;

      TermList candidate = _terms[_next];
      _assumptions.push(~Minisat::mkLit(_next));

      _substitution->reset();
      if(_substitution->unify(_query, 0, candidate, 1)) {
        _next++;
        return candidate;
      }
      else
        explain(candidate, _next);
    }
    if(!_solver.solve(_assumptions))
      return empty;

    _next = 0;
  }
}

struct Unify {
  unsigned position;
  TermList query;
  TermList candidate;
};

void SATIndex::explain(TermList candidate, unsigned candidateVariable) {
  CALL("SATIndex::explain")

  Minisat::Lit candidateLiteral = Minisat::mkLit(candidateVariable);
  Stack<Unify> todo;
  todo.push({0, _query, candidate});
  while(todo.isNonEmpty()) {
    Unify next = todo.pop();
    if(next.query.isVar() || next.candidate.isVar())
      continue;

    Term *query = next.query.term();
    Term *candidate = next.candidate.term();
    if(query->functor() != candidate->functor()) {
      Minisat::Lit querySymbol = symbolOccursAt(query->functor(), next.position);
      Minisat::Lit candidateSymbol = symbolOccursAt(candidate->functor(), next.position);

      if(_termSymbols.insert({candidateVariable, var(candidateSymbol)}))
        _solver.addClause(~candidateLiteral, candidateSymbol);

      if(querySymbol < candidateSymbol)
        std::swap(querySymbol, candidateSymbol);

      if(_symbolMismatches.insert({var(querySymbol), var(candidateSymbol)}))
        _solver.addClause(~querySymbol, ~candidateSymbol);

      return;
    }

    for(unsigned i = 0; i < query->arity(); i++)
      todo.push({position(next.position, i), (*query)[i], (*candidate)[i]});
  }
  //std::cout << "cannot explain: " << _query.toString() << " != " << candidate.toString() << std::endl;
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

Minisat::Lit SATIndex::symbolOccursAt(unsigned functor, unsigned position) {
  CALL("SATIndex::symbolOccursAt")
  Minisat::Lit *literal;
  if(_symbolsOccurAt.getValuePtr({functor, position}, literal))
    *literal = freshLiteral();

  return *literal;
}

unsigned SATIndex::position(unsigned parent, unsigned argument) {
  CALL("SATIndex::termLiteral")
  unsigned result = _positions.findOrInsert({parent, argument}, _positions.size() + 1);
  return result;
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
