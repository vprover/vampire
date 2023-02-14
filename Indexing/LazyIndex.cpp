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

void Positions::setTerm(TermList term) {
  static Stack<unsigned> clear;
  clear.push(0);
  while(clear.isNonEmpty()) {
    unsigned next = clear.pop();
    _positions[next].term.makeEmpty();
    for(unsigned i = 0; i < _positions[next].children.size(); i++)
      if(_positions[_positions[next].children[i]].term.isNonEmpty())
        clear.push(_positions[next].children[i]);
  }

  static Stack<std::pair<unsigned, TermList>> todo;
  todo.push({ 0, term });
  while(todo.isNonEmpty()) {
    std::pair<unsigned, TermList> next = todo.pop();
    unsigned position = std::get<0>(next);
    TermList term = std::get<1>(next);
    _positions[position].term = term;
    if(term.isTerm()) {
      Term *compound = term.term();
      for(unsigned i = 0; i < compound->arity(); i++)
        todo.push({ child(position, i), (*compound)[i] });
    }
  }
}

TermList Positions::term_at(unsigned position, bool &outside_term, bool &under_variable) {
  CALL("Positions::term_at")

  if(_positions[position].term.isNonEmpty())
    return _positions[position].term;

  while(true) {
    unsigned parent = _positions[position].parent;
    if(_positions[parent].term.isEmpty()) {
      position = parent;
      continue;
    }

    TermList term = _positions[parent].term;
    if(term.isVar())
      under_variable = true;
    else
      outside_term = true;
    return term;
  }
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

struct Binding {
  TermList bound;
  unsigned position;
};

template<bool instantiate, bool generalise>
LazyIndex::Reason LazyIndex::explain(TermList candidate) {
  CALL("LazyIndex::explain")

  // TODO used Recycled<T>
  static Stack<Unify> unify;
  unify.reset();
  unify.push({
    .query = _query,
    .candidate = candidate,
    .position = 0
  });
  static DHMap<unsigned, Binding> candidate_bindings;
  if(generalise)
    candidate_bindings.reset();

  while(unify.isNonEmpty()) {
    Unify next = unify.pop();
    unsigned position = next.position;
    TermList query = next.query;
    TermList candidate = next.candidate;

    if(!generalise && query.isTerm() && candidate.isVar()) {
      explanation_position = position;
      return Reason::VARIABLE;
    }

    if(!instantiate && query.isVar() && !candidate.isVar()) {
      explanation_position = position;
      explanation_candidate_functor = candidate.term()->functor();
      return Reason::SYMBOL;
    }

    Binding binding;
    if(
      generalise &&
      candidate.isVar() &&
      !candidate_bindings.findOrInsert(
        candidate.var(),
        binding,
        { .bound = query, .position = position }
      ) &&
      (
        (instantiate && (_substitution->reset(), !_substitution->unify(query, 0, binding.bound, 0))) ||
        (!instantiate && query != binding.bound)
      )
    ) {
      explanation_position = position;
      explanation_other_position = binding.position;
      return Reason::ALIAS;
    }

    if(query.isVar() || candidate.isVar())
      continue;

    Term *query_term = query.term();
    Term *candidate_term = candidate.term();
    if(query_term->functor() != candidate_term->functor()) {
      explanation_position = position;
      explanation_candidate_functor = candidate_term->functor();
      return Reason::MISMATCH;
    }

    for(unsigned i = 0; i < query_term->arity(); i++) {
      unsigned argument_position = _positions.child(position, i);
      unify.push({
        .query = (*query_term)[i],
        .candidate = (*candidate_term)[i],
        .position = argument_position
      });
    }
  }

  const char *syms[2][2] = {{" * ", " <- "}, {" -> ", " = "}};
  std::cout << _query.toString() << syms[instantiate][generalise] << candidate.toString() << std::endl;

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

  Query(LazyIndex &index, TermList query) : _index(index) {
    _index.setQuery(query);
    _todo.push(Iteration(index._root));
    _next.makeEmpty();
  }

  bool hasNext();
  TermList next() {
    CALL("LazyIndex::Query::next")
    ASS(!_next.isEmpty())
    TermList next = _next;
    _next.makeEmpty();
    return next;
  }

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
      functor_positions(branch.functor_positions),
      aliases(branch.aliases) {}

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
    // aliases we should consider after that
    DHMap<std::pair<unsigned, unsigned>, Branch>::DelIterator aliases;
  };

  // the index we're querying
  LazyIndex &_index;
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

  if(!_next.isEmpty())
    return true;

  RobSubstitution &substitution = *_index._substitution;
  while(_todo.isNonEmpty()) {
new_branch:
    Iteration &iteration = _todo.top();

    while(iteration.immediate.hasNext()) {
      TermList candidate = iteration.immediate.next();

      if(_index._remove.remove(candidate)) {
        iteration.immediate.del();
        continue;
      }

      substitution.reset();
      bool ok;
      if(instantiate && generalise)
        ok = substitution.unify(_index._query, 0, candidate, 1);
      else if(instantiate && !generalise)
        ok = substitution.match(_index._query, 0, candidate, 1);
      else if(!instantiate && generalise)
        ok = substitution.match(candidate, 1, _index._query, 0);
      else
        NOT_IMPLEMENTED;

      if(ok) {
        _next = candidate;
        return true;
      }

      Reason reason = _index.explain<instantiate, generalise>(candidate);
      if(reason)
        iteration.immediate.del();

      switch(reason) {
        case Reason::NO_REASON:
          continue;
        case Reason::MISMATCH:
        case Reason::SYMBOL:
        {
          ASS(!instantiate || reason == Reason::MISMATCH)

          FunctorsAt *functors_at;
          iteration.branch.functor_positions.getValuePtr(_index.explanation_position, functors_at);
          // iterator might be invalidated by new entry
          iteration.functor_positions.~DelIterator();
          ::new(&iteration.functor_positions) decltype(iteration.functor_positions)(iteration.branch.functor_positions);

          Branch *child;
          functors_at->functors.getValuePtr(_index.explanation_candidate_functor, child);
          child->immediate.push(candidate);
          break;
        }
        case Reason::VARIABLE:
        {
          ASS(!generalise)

          Branch *child;
          iteration.branch.variable_positions.getValuePtr(_index.explanation_position, child);
          // iterator might be invalidated by new entry
          iteration.variable_positions.~DelIterator();
          ::new(&iteration.variable_positions) decltype(iteration.variable_positions)(iteration.branch.variable_positions);

          child->immediate.push(candidate);
          break;
        }
        case Reason::ALIAS:
        {
          ASS(generalise)

          Branch *child;
          iteration.branch.aliases.getValuePtr({ _index.explanation_position, _index.explanation_other_position }, child);
          // iterator might be invalidated by new entry
          iteration.aliases.~DelIterator();
          ::new(&iteration.aliases) decltype(iteration.aliases)(iteration.branch.aliases);

          child->immediate.push(candidate);
          break;
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

      bool outside_term = false, under_variable = false;
      TermList subterm = _index._positions.term_at(position, outside_term, under_variable);
      if(
        outside_term ||
        (!instantiate && under_variable) ||
        (!generalise && subterm.isTerm())
      )
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

      bool outside_term = false, under_variable = false;
      TermList subterm = _index._positions.term_at(position, outside_term, under_variable);
      if(outside_term)
        continue;

      if(instantiate && subterm.isVar()) {
        ASS(!iteration.branches.hasNext())
        iteration.branches.~DelIterator();
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

    while(iteration.aliases.hasNext()) {
      std::pair<unsigned, unsigned> alias;
      Branch &branch = iteration.aliases.nextRef(alias);

      if(branch.isEmpty()) {
        iteration.aliases.del();
        continue;
      }

      bool outside_term1 = false, under_variable1 = false;
      TermList subterm1 = _index._positions.term_at(std::get<0>(alias), outside_term1, under_variable1);
      if(outside_term1 || (!instantiate && under_variable1) || (!generalise && subterm1.isTerm()))
        continue;

      bool outside_term2 = false, under_variable2 = false;
      TermList subterm2 = _index._positions.term_at(std::get<1>(alias), outside_term2, under_variable2);
      if(outside_term2 || (!instantiate && under_variable2) || (!generalise && subterm2.isTerm()))
        continue;

      if(
        (!instantiate && subterm1 != subterm2) ||
        (instantiate && (substitution.reset(), !substitution.unify(subterm1, 0, subterm2, 0)))
      )
        continue;

      _todo.push(Iteration(branch));
      goto new_branch;
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

TermQueryResultIterator LazyTermIndex::getGeneralizations(TermList query, bool retrieveSubstitutions) {
  CALL("LazyTermIndex::getGeneralizations")
  return get<false, true>(query);
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

SLQueryResultIterator LazyLiteralIndex::getGeneralizations(Literal* query, bool complementary, bool retrieveSubstitutions) {
  CALL("LazyLiteralIndex::getGeneralizations")
  return get<false, true>(query, complementary);
}

SLQueryResultIterator LazyLiteralIndex::getInstances(Literal* query, bool complementary, bool retrieveSubstitutions) {
  CALL("LazyLiteralIndex::getInstances")
  return get<true, false>(query, complementary);
}

} //namespace Indexing
