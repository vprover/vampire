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
#include "Lib/Stack.hpp"
#include "Kernel/RobSubstitution.hpp"

namespace Indexing {

class LazyIndex {
public:
  LazyIndex() :
    _substitution(new RobSubstitution),
    substitution(ResultSubstitution::fromSubstitution(_substitution, 0, 1))
  {}
  ~LazyIndex() { delete _substitution; }

  void insert(TermList t);

private:
  struct Node {
    Stack<TermList> terms;
  };

  struct Position {
    Node &node;
    unsigned index;
  };

  Node _root;
  RobSubstitution *_substitution;

public:
  ResultSubstitutionSP substitution;

  class Iterator {
  public:
    DECL_ELEMENT_TYPE(TermList);

    Iterator(LazyIndex &index, TermList query) : _substitution(*index._substitution), _query(query) {
      std::cout << "query: " << query.toString() << std::endl;
      _positions.push({
        .node = index._root,
        .index = 0
      });
    }

    bool hasNext();
    TermList next() { return _next; }


  private:
    Stack<Position> _positions;
    RobSubstitution &_substitution;
    TermList _next, _query;
  };
};

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
  LazyIndex _index;

  struct Entry {
    Literal *literal;
    Clause *clause;
  };

  DHMap<TermList, Stack<Entry>> _entries;
};

} //namespace Indexing

#endif
