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
 * @file SATIndex.hpp
 * Term indices based on an internal SAT solver
 */


#ifndef __SATIndex__
#define __SATIndex__

#include "TermIndex.hpp"
#include "Minisat/core/Solver.h"

namespace Indexing {

class SATIndex {
public:
  CLASS_NAME(SATIndex)
  USE_ALLOCATOR(SATIndex)

  // create an empty SAT index
  SATIndex();
  ~SATIndex();

  // insert `term` into the index
  void insert(TermList term);

  // the subsitution for the most recent iterator result
  ResultSubstitutionSP substitution;

  class Unifications {
  public:
    DECL_ELEMENT_TYPE(TermList);
    Unifications(SATIndex &index, TermList query) : index(index) {
      index.prepareUnifications(query);
      result.makeEmpty();
    };
    bool hasNext() { return result.isNonEmpty() || (result = index.next()).isNonEmpty(); }
    TermList next() {
      TermList next = result;
      result.makeEmpty();
      return next;
    }

  private:
    SATIndex &index;
    TermList result;
  };

private:
  // prepare to return unifications of `query`
  void prepareUnifications(TermList query);

  // return next query result, empty if no more results
  TermList next();

  // create a new positive literal
  Minisat::Lit freshLiteral();
  // create a new positive literal for a term
  Minisat::Lit freshTermLiteral(TermList term);

  // the current query term
  TermList _query;

  // internal substitution object
  RobSubstitution *_substitution;

  // the underlying SAT solver
  Minisat::Solver _solver;

  // a list of assumptions for the SAT solver
  Minisat::vec<Minisat::Lit> _assumptions;

  // the last link variable used
  Minisat::Lit _lastLink;

  // terms, indexed by SAT variables - empty if no term associated with a variable
  Stack<TermList> _terms;

  // next term to check in the model
  unsigned _next;
};

class SATTermIndex: public TermIndexingStructure {
public:
  CLASS_NAME(SATTermIndex)
  USE_ALLOCATOR(SATTermIndex)
  virtual void insert(TermList term, Literal *literal, Clause *clause);
  virtual void remove(TermList term, Literal *literal, Clause *clause);
  virtual void insert(TermList t1, TermList t2){ NOT_IMPLEMENTED; }
  virtual void insert(TermList t1, TermList t2, Literal *literal, Clause *clause){ NOT_IMPLEMENTED; }

  virtual TermQueryResultIterator getUnifications(TermList term, bool retrieveSubstitutions = true);
  virtual TermQueryResultIterator getUnificationsUsingSorts(TermList t, TermList sort, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual TermQueryResultIterator getUnificationsWithConstraints(TermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual TermQueryResultIterator getGeneralizations(TermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual TermQueryResultIterator getInstances(TermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual bool generalizationExists(TermList t) { NOT_IMPLEMENTED; }

#if VDEBUG
  virtual void markTagged() { NOT_IMPLEMENTED; }
#endif

private:
  // currently just a literal, clause pair
  struct Entry {
    Literal *literal;
    Clause *clause;
  };

  // underlying index
  SATIndex _index;
  // map from terms to entries
  DHMap<TermList, Stack<Entry>> _entries;
};

};

#endif /* __SATIndex__ */
