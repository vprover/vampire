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
  while(_positions[parent].children.size() <= argument) {
    unsigned child = _positions.size();
    unsigned argument = _positions[parent].children.size();
    _positions.push(PositionData(parent, argument));
    _positions[parent].children.push(child);
  }
  return _positions[parent].children[argument];
}

TermList Positions::term_at(TermList term, unsigned position) {
  CALL("Positions::term_at")

  // TODO used Recycled<T>
  static Stack<unsigned> arguments;
  arguments.reset();

  while(position) {
    arguments.push(_positions[position].argument);
    position = _positions[position].parent;
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

void LazyIndex::insert(TermList t) {
  CALL("LazyIndex::insert")
  if(!_remove.remove(t))
    _root.immediate.push(t);
}

struct Unify {
  TermList query;
  TermList candidate;
  unsigned position;
};

template<bool instantiate, bool generalise>
LazyIndex::Reason LazyIndex::explain(TermList query, TermList candidate) {
  CALL("LazyIndex::explain")

  // TODO used Recycled<T>
  static Stack<Unify> unify;
  unify.reset();
  unify.push({
    .query = query,
    .candidate = candidate,
    .position = 0
  });

  while(unify.isNonEmpty()) {
    Unify next = unify.pop();

    unsigned position = next.position;
    if(!generalise && !next.query.isVar() && next.candidate.isVar()) {
      explanation_position = position;
      return Reason::VARIABLE;
    }

    if(next.query.isVar() || next.candidate.isVar())
      continue;

    Term *query = next.query.term();
    Term *candidate = next.candidate.term();
    if(query->functor() != candidate->functor()) {
      explanation_position = position;
      explanation_candidate_functor = candidate->functor();
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

/**
 * Iterate over terms in an index that match a given query term
 *
 * If `instantiate`, variables in the query may be bound
 * If `generalise`, variables in the candidates may be bound
 */
template<bool instantiate, bool generalise>
class LazyIndex::Query {
public:
  DECL_ELEMENT_TYPE(TermList);

  Query(LazyIndex &index, TermList query) : _index(index), _query(query) {
    _todo.push(Iteration(index._root));
#if VDEBUG
    _next.makeEmpty();
#endif
  }

  bool hasNext();
  TermList next() { return _next; }

private:
  // dummy to allow empty iterators
  static DHMap<unsigned, Branch> EMPTY_BRANCH_MAP;

  // keep track of how far we have made it through a certain `branch`
  struct Iteration {
    Iteration(Branch &branch) :
      branch(branch),
      immediate(branch.immediate),
      branches(EMPTY_BRANCH_MAP),
      variable_positions(branch.variable_positions),
      functor_positions(branch.functor_positions) {}

    // the branch we're iterating over
    Branch &branch;
    // the terms stored in the branch we should consider first
    Stack<TermList>::Iterator immediate;
    // child branches we should consider next
    DHMap<unsigned, Branch>::DelIterator branches;
    // variable positions we should consider after that
    DHMap<unsigned, Branch>::DelIterator variable_positions;
    // functor positions we should consider after that
    DHMap<unsigned, FunctorsAt>::DelIterator functor_positions;
  };

  // the index we're querying
  LazyIndex &_index;
  // the query term
  TermList _query;
  // a stack of partially-iterated branches
  Stack<Iteration> _todo;
  // found a suitable term, will be returned by `next()`
  TermList _next;
};

template<bool instantiate, bool generalise>
DHMap<unsigned, LazyIndex::Branch> LazyIndex::Query<instantiate, generalise>::EMPTY_BRANCH_MAP;

template<bool instantiate, bool generalise>
bool LazyIndex::Query<instantiate, generalise>::hasNext() {
  CALL("LazyIndex::Query::hasNext")

  while(_todo.isNonEmpty()) {
new_branch:
    Iteration &iteration = _todo.top();

    while(iteration.immediate.hasNext()) {
      TermList candidate = iteration.immediate.next();

      if(_index._remove.remove(candidate)) {
        iteration.immediate.del();
        continue;
      }

      RobSubstitution &substitution = *_index._substitution;
      substitution.reset();
      bool ok;
      if(instantiate && generalise)
        ok = substitution.unify(_query, 0, candidate, 1);
      else if(instantiate && !generalise)
        ok = substitution.match(_query, 0, candidate, 1);
      else
        NOT_IMPLEMENTED;

      if(ok) {
        _next = candidate;
        return true;
      }

      Reason reason = _index.explain<instantiate, generalise>(_query, candidate);
      switch(reason) {
        case Reason::NO_REASON:
          continue;
        case Reason::MISMATCH:
        {
          iteration.immediate.del();
          FunctorsAt *functors_at;
          iteration.branch.functor_positions.getValuePtr(_index.explanation_position, functors_at);
          // iterator might be invalidated by new entry
          ::new(&iteration.functor_positions) decltype(iteration.functor_positions)(iteration.branch.functor_positions);

          Branch *child;
          functors_at->functors.getValuePtr(_index.explanation_candidate_functor, child);
          child->immediate.push(candidate);
          break;
        }
        case Reason::VARIABLE:
        {
          ASS(!generalise);
          iteration.immediate.del();

          Branch *child;
          iteration.branch.variable_positions.getValuePtr(_index.explanation_position, child);
          // iterator might be invalidated by new entry
          ::new(&iteration.variable_positions) decltype(iteration.variable_positions)(iteration.branch.variable_positions);

          child->immediate.push(candidate);
        }
      }
    }

new_branches:
    while(iteration.branches.hasNext()) {
      Branch &branch = iteration.branches.nextRef();

      if(branch.isEmpty()) {
        iteration.branches.del();
        continue;
      }

      _todo.push(Iteration(branch));
      goto new_branch;
    }

    while(iteration.variable_positions.hasNext()) {
      unsigned position;
      Branch &branch = iteration.variable_positions.nextRef(position);

      if(branch.isEmpty()) {
        iteration.variable_positions.del();
        continue;
      }

      if(!generalise && _index._positions.term_at(_query, position).isTerm())
        continue;

      _todo.push(Iteration(branch));
      goto new_branch;
    }

    while(iteration.functor_positions.hasNext()) {
      unsigned position;
      FunctorsAt &functor_at = iteration.functor_positions.nextRef(position);

      if(functor_at.isEmpty()) {
        iteration.functor_positions.del();
        continue;
      }

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
  DHSet<Entry> *entry;
  if(_entries.getValuePtr(t, entry))
    _index.insert(t);

  entry->insert({lit, cls});
}

void LazyTermIndex::remove(TermList t, Literal *lit, Clause *cls) {
  CALL("LazyTermIndex::remove")
  DHSet<Entry> &entries = _entries.get(t);
  entries.remove({lit, cls});
  if(entries.isEmpty()) {
    _entries.remove(t);
    _index.remove(t);
  }
}

template<bool instantiate, bool generalise>
TermQueryResultIterator LazyTermIndex::get(TermList query) {
  CALL("LazyTermIndex::get")
  return pvi(getMapAndFlattenIterator(
    LazyIndex::Query<instantiate, generalise>(_index, query),
    [this](TermList result) {
      return pvi(getMappingIterator(
        DHSet<Entry>::Iterator(_entries.get(result)),
        [this, result](Entry entry) {
          return TermQueryResult(result, entry.first, entry.second, _index.substitution);
        }
      ));
  }));
}

TermQueryResultIterator LazyTermIndex::getUnifications(TermList query, bool retrieveSubstitutions) {
  CALL("LazyTermIndex::getUnifications")
  return get<true, true>(query);
}

TermQueryResultIterator LazyTermIndex::getInstances(TermList query, bool retrieveSubstitutions) {
  CALL("LazyTermIndex::getInstances")
  return get<true, false>(query);
}

void LazyLiteralIndex::insert(Literal* lit, Clause* cls) {
  CALL("LazyLiteralIndex::insert(Literal *, Clause *)")

  DHSet<Clause *> *entry;
  if(_entries.getValuePtr(lit, entry))
    _indices[lit->polarity()].insert(TermList(lit));

  entry->insert(cls);
}

void LazyLiteralIndex::remove(Literal *lit, Clause *cls) {
  CALL("LazyLiteralIndex::remove")

  DHSet<Clause *> &entry = _entries.get(lit);
  entry.remove(cls);
  if(entry.isEmpty()) {
    _entries.remove(lit);
    _indices[lit->polarity()].remove(TermList(lit));
  }
}

template<bool instantiate, bool generalise>
SLQueryResultIterator LazyLiteralIndex::get(Literal* query, bool complementary) {
  CALL("LazyLiteralIndex::get")
  LazyIndex &index = _indices[query->polarity() ^ complementary];
  return pvi(getMapAndFlattenIterator(
    LazyIndex::Query<instantiate, generalise>(index, TermList(query)),
    [this, &index](TermList result_term) {
      Literal *result = static_cast<Literal *>(result_term.term());
      return pvi(getMappingIterator(
        DHSet<Clause *>::Iterator(_entries.get(result)),
        [&index, result](Clause *clause) {
          return SLQueryResult(result, clause, index.substitution);
        }
      ));
  }));
}

SLQueryResultIterator LazyLiteralIndex::getUnifications(Literal* query, bool complementary, bool retrieveSubstitutions) {
  CALL("LazyLiteralIndex::getUnifications")
  return get<true, true>(query, complementary);
}

SLQueryResultIterator LazyLiteralIndex::getInstances(Literal* query, bool complementary, bool retrieveSubstitutions) {
  CALL("LazyLiteralIndex::getInstances")
  return get<true, false>(query, complementary);
}

} //namespace Indexing
