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
 * @file LazyIndex.hpp
 * Lazy term indexing
 */

#ifndef __LazyIndex__
#define __LazyIndex__

#include "TermIndexingStructure.hpp"
#include "LiteralIndexingStructure.hpp"

#include "Lib/Hash.hpp"
#include "Lib/Stack.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/RobSubstitution.hpp"

namespace Indexing {

/**
 * A compact representation of positions within terms.
 *
 * Each position `p.n` is represented by an index into `_entries`.
 * The corresponding entry tracks its parent `p`, argument `n` and children.
 * The empty term is index 0, with parent and argument 0
 */
class Positions {
public:
  Positions() { _positions.push(PositionData(0, 0)); }
  void setTerm(TermList term);

  // get the integer representing `p.n`
  unsigned child(unsigned parent, unsigned argument);
  // if child is `p.n`, return `p`
  unsigned parent(unsigned child) { return _positions[child].parent; }
  // if child is `p.n`, return `n`
  unsigned argument(unsigned child) { return _positions[child].argument; }

  /**
  * retrieve the sub-term at `position`
  *
  * - if the position is not in the term, `outside_term` is set
  * - if the position is under a variable, `under_variable` is set and the variable returned
  * - otherwise the subterm is returned
  */
  TermList term_at(unsigned position, bool &outside_term, bool &under_variable);

private:
  /**
   * Data held for a position
   */
  struct PositionData {
    PositionData(unsigned parent, unsigned argument) : parent(parent), argument(argument) {
      term.makeEmpty();
    }
    // if a position is `p.n`, `p`
    unsigned parent;
    // if a position is `p.n`, `n`
    unsigned argument;
    // positions of the form `p.n.m`
    Stack<unsigned> children;
    // the current term at this position, or empty
    TermList term;
  };

  // all positions seen so far
  Stack<PositionData> _positions;
};

/**
 * A lazy term index.
 *
 * Essentially just a queryable set of `TermList`, use e.g. `LazyTermIndex` for a higher-level interface.
 */
class LazyIndex {
public:
  // An empty index
  LazyIndex() :
    _substitution(new RobSubstitution),
    substitution(ResultSubstitution::fromSubstitution(_substitution, 0, 1)) {}

  // insert `t` into the index, very lazily
  void insert(TermList t);

  // remove `t` from the index, very lazily
  void remove(TermList t) { _remove.insert(t); }

private:
  // an iterator returning results of a query
  template<bool instantiate, bool generalise>
  class Query;

  void setQuery(TermList query) {
    _query = query;
    _positions.setTerm(query);
  }

  // reasons that a candidate term might not satisfy a query
  enum Reason {
    // no reason could be determined
    NO_REASON = 0,
    // the candidate and the query have different symbols at a position
    MISMATCH,
    // the candidate has a variable where the query has a symbol, but we don't want generalisations
    VARIABLE,
    // the candidate has a symbol where the query has a variable, but we don't want instances
    SYMBOL,
    // the candidate has a repeated variable in a position incompatible with the query
    ALIAS
  };

  /**
   * try and explain why `candidate` does not satisfy `query`
   *
   * if `instantiate`, variables in `query` may be bound
   * if `generalise`, variables in `candidate` may be bound
   */
  template<bool instantiate, bool generalise>
  Reason explain(TermList candidate);

  /**
   * if `explain(query, candidate)` returned `MISMATCH` or `SYMBOL`:
   * - `explanation_position` is one failed position
   * - `explanation_candidate_functor` is the candidate's functor at `mismatch_position`
   * if `explain(query, candidate)` returned `VARIABLE`:
   * - `explanation_position` is one position of a variable in the candidate where the query has a symbol
   * if `explain(query, candidate)` returned `ALIAS`:
   * - `explanation_position` is one position of a repeated variable in the candidate
   * - `explanation_other_position` is another
   */
  unsigned explanation_position, explanation_candidate_functor, explanation_other_position;

  // forward decl for mutually-recursive struct
  struct FunctorsAt;

  // the basic tree type, stores terms and sub-trees constraining terms
  struct Branch {
    // move-only structure, should never need copying
    Branch() = default;
    Branch(Branch &&) = default;
    Branch &operator=(Branch &&) = default;

    // the terms stored at this node
    Stack<TermList> immediate;

    // subtrees where terms have a variable at a position
    DHMap<unsigned, Branch> variable_positions;

    // subtrees where terms have a known functor at a position
    DHMap<unsigned, FunctorsAt> functor_positions;

    // subtrees where terms have the same variable at two positions
    DHMap<std::pair<unsigned, unsigned>, Branch> aliases;

    // is this an empty node suitable for deletion?
    bool isEmpty() {
      return immediate.isEmpty() &&
        variable_positions.isEmpty() &&
        functor_positions.isEmpty() &&
        aliases.isEmpty();
    }
  };

  // represents a choice of known functors at a position
  struct FunctorsAt {
    // move-only structure, should never need copying
    FunctorsAt() = default;
    FunctorsAt(FunctorsAt &&) = default;
    FunctorsAt &operator=(FunctorsAt &&) = default;

    // functors at this position
    DHMap<unsigned, Branch> functors;

    // is this an empty node suitable for deletion?
    bool isEmpty() { return functors.isEmpty(); }
  };

  // the root of the indexing tree
  Branch _root;
  // all positions seen so far
  Positions _positions;
  // an underlying substitution object for `substitution`
  RobSubstitution *_substitution;

  // terms that we should remove, but haven't actually removed yet
  DHSet<TermList> _remove;

  // the current query term
  TermList _query;

public:
  /**
   * if an iterator just returned `candidate` from `next()`, this is the unifier of `query` and `candidate`
   * NB: this is invalidated by a subsequent call to `hasNext()`
   */
  ResultSubstitutionSP substitution;
};

/**
 * Wrapper around `LazyIndex` for term indexing
 */
class LazyTermIndex: public TermIndexingStructure {
public:
  CLASS_NAME(LazyTermIndex);
  USE_ALLOCATOR(LazyTermIndex);

  void insert(TermList t, Literal* lit, Clause* cls) override;
  void remove(TermList t, Literal* lit, Clause* cls) override;
  void insert(TermList t, TermList trm) override { NOT_IMPLEMENTED; }
  void insert(TermList t, TermList trm, Literal* lit, Clause* cls) override { NOT_IMPLEMENTED; }

  template<bool instantiate, bool generalise>
  TermQueryResultIterator get(TermList t);

  TermQueryResultIterator getUnifications(TermList t, bool retrieveSubstitutions = true) override;
  TermQueryResultIterator getUnificationsUsingSorts(TermList t, TermList sort, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }
  TermQueryResultIterator getUnificationsWithConstraints(TermList t, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }
  TermQueryResultIterator getGeneralizations(TermList t, bool retrieveSubstitutions = true) override;
  TermQueryResultIterator getInstances(TermList t, bool retrieveSubstitutions = true) override;

  bool generalizationExists(TermList t) override { NOT_IMPLEMENTED; }

#if VDEBUG
  void markTagged() override { NOT_IMPLEMENTED; }
#endif

private:
  // the underlying index
  LazyIndex _index;

  using Entry = std::pair<Literal *, Clause *>;
  // map from indexed terms to one or more literal/clause pairs
  DHMap<TermList, DHSet<Entry>> _entries;
};

class LazyLiteralIndex: public LiteralIndexingStructure {
public:
  CLASS_NAME(LazyLiteralIndex);
  USE_ALLOCATOR(LazyLiteralIndex);
  void insert(Literal* lit, Clause* cls) override;
  void remove(Literal* lit, Clause* cls) override;

  template<bool instantiate, bool generalise>
  SLQueryResultIterator get(Literal *lit, bool complementary);

  SLQueryResultIterator getAll() override { NOT_IMPLEMENTED; }
  SLQueryResultIterator getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions = true) override;
  SLQueryResultIterator getUnificationsWithConstraints(Literal* lit, bool complementary, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }
  SLQueryResultIterator getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions = true) override;
  SLQueryResultIterator getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions = true) override;
  SLQueryResultIterator getVariants(Literal* lit, bool complementary, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }

#if VDEBUG
  vstring toString() override { NOT_IMPLEMENTED; }
  void markTagged() override { NOT_IMPLEMENTED; }
#endif

private:
  // the underlying indices, one for each polarity
  LazyIndex _indices[2];

  // map from indexed literals to one or more clauses
  DHMap<Literal *, DHSet<Clause *>> _entries;
};

} //namespace Indexing

#endif
