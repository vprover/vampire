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
  Positions() { _entries.push(Entry(0, 0)); }

  // get the integer representing `p.n`
  unsigned child(unsigned parent, unsigned argument);
  // if child is `p.n`, return `p`
  unsigned parent(unsigned child) { return _entries[child].parent; }
  // if child is `p.n`, return `n`
  unsigned argument(unsigned child) { return _entries[child].argument; }

  /**
  * retrieve the sub-term of `term` at `position`
  *
  * special cases:
  * - returns a variable if below said variable
  * - returns an empty term if position does not exist in the term
  */
  TermList term_at(TermList term, unsigned position);

private:
  /**
   * Data representing a position.
   */
  struct Entry {
    Entry(unsigned parent, unsigned argument) : parent(parent), argument(argument) {}
    // if a position is `p.n`, `p`
    unsigned parent;
    // if a position is `p.n`, `n`
    unsigned argument;
    // positions of the form `p.n.m`
    Stack<unsigned> children;
  };

  // all positions seen so far
  Stack<Entry> _entries;
};

/**
 * A lazy term index.
 *
 * Essentially just a set of `TermList`, use e.g. `LazyTermIndex` for a higher-level interface.
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

  // reasons that a candidate term might not satisfy a query
  enum class Reason {
    // no reason could be determined
    NO_REASON,
    // the candidate and the query have different function symbols at a position
    MISMATCH
  };

  // try and explain why `candidate` does not satisfy `query`
  Reason explain(TermList query, TermList candidate);

  /**
   * if `explain(query, candidate)` returned `MISMATCH`:
   * - `mismatch_position` is one position where they differ
   * - `mismatch_candidate_functor` is the candidate's functor at `mismatch_position`
   */
  unsigned mismatch_position, mismatch_candidate_functor;

private:
  // forward decl for mutually-recursive struct
  struct FunctorAt;

  // the basic tree type, stores terms and sub-trees constraining terms
  struct Branch {
    // move-only structure, should never need copying
    Branch() = default;
    Branch(Branch &&) = default;
    Branch &operator=(Branch &&) = default;

    // the terms stored at this node
    Stack<TermList> immediate;

    // subtrees where terms have a known functor at a position
    DHMap<unsigned, FunctorAt> positions;

    // is this an empty node suitable for deletion?
    bool isEmpty() { return immediate.isEmpty() && positions.isEmpty(); }
  };

  // represents a choice of known functors at a position
  struct FunctorAt {
    // move-only structure, should never need copying
    FunctorAt() = default;
    FunctorAt(FunctorAt &&) = default;
    FunctorAt &operator=(FunctorAt &&) = default;

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

public:
  // if an `Iterator` just returned `candidate`, this is the unifier of `query` and `candidate`
  ResultSubstitutionSP substitution;

  /**
   * Iterate over terms in an index that match a given query
   */
  class QueryIterator {
  public:
    DECL_ELEMENT_TYPE(TermList);

    QueryIterator(LazyIndex &index, TermList query) : _index(index), _query(query) {
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
        functors(branch.positions) {}

      // the branch we're iterating over
      Branch &branch;
      // the terms stored in the branch we should consider first
      Stack<TermList>::Iterator immediate;
      // child branches we should consider next
      DHMap<unsigned, Branch>::DelIterator branches;
      // positions we should consider after that
      DHMap<unsigned, FunctorAt>::DelIterator functors;
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

  TermQueryResultIterator getUnifications(TermList t, bool retrieveSubstitutions = true) override;
  TermQueryResultIterator getUnificationsUsingSorts(TermList t, TermList sort, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }
  TermQueryResultIterator getUnificationsWithConstraints(TermList t, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }
  TermQueryResultIterator getGeneralizations(TermList t, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }
  TermQueryResultIterator getInstances(TermList t, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }

  bool generalizationExists(TermList t) override { NOT_IMPLEMENTED; }

#if VDEBUG
  void markTagged() override { NOT_IMPLEMENTED; }
#endif

private:
  // the underlying index
  LazyIndex _index;

  // what we store in the index, could be custom data in future
  struct Entry {
    Literal *literal;
    Clause *clause;

    bool operator==(const Entry &other) const {
      return literal == other.literal && clause == other.clause;
    }
    bool operator!=(const Entry &other) const {
      return !operator==(other);
    }

    unsigned defaultHash() const {
      return DefaultHash::hash(literal, DefaultHash::hash(clause));
    }

    unsigned defaultHash2() const {
      return HashUtils::combine(DefaultHash2::hash(literal), DefaultHash2::hash(clause));
    }
  };

  // map from indexed terms to one or more `Entry`s
  DHMap<TermList, DHSet<Entry>> _entries;
};

class LazyLiteralIndex: public LiteralIndexingStructure {
public:
  CLASS_NAME(LazyLiteralIndex);
  USE_ALLOCATOR(LazyLiteralIndex);
  void insert(Literal* lit, Clause* cls) override;
  void remove(Literal* lit, Clause* cls) override;

  SLQueryResultIterator getAll() override { NOT_IMPLEMENTED; }
  SLQueryResultIterator getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions = true) override;
  SLQueryResultIterator getUnificationsWithConstraints(Literal* lit, bool complementary, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }
  SLQueryResultIterator getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }
  SLQueryResultIterator getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions = true) override { NOT_IMPLEMENTED; }
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
