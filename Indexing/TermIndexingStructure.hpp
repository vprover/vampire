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
 * @file TermIndexingStructure.hpp
 * Defines class TermIndexingStructure.
 */


#ifndef __TermIndexingStructure__
#define __TermIndexingStructure__

#include "Index.hpp"

namespace Indexing {

class TermIndexingStructure {
public:
  virtual ~TermIndexingStructure() {}

  virtual void insert(TypedTermList t, Literal* lit, Clause* cls) = 0;
  virtual void remove(TypedTermList t, Literal* lit, Clause* cls) = 0;
  void handle(TypedTermList t, Literal* lit, Clause* cls, bool insert) 
  { if (insert) { this->insert(t, lit, cls); } else { remove(t, lit, cls); } }
  virtual void insert(TypedTermList t, TermList trm){ NOT_IMPLEMENTED; }
  virtual void insert(TypedTermList t, TermList trm, Literal* lit, Clause* cls){ NOT_IMPLEMENTED; }

  virtual TermQueryResultIterator getUnifications(TypedTermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<TQueryRes<AbstractingUnifier*>> getUwa(TypedTermList t, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) = 0;
  virtual TermQueryResultIterator getUnificationsUsingSorts(TypedTermList tt, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }  
  virtual TermQueryResultIterator getGeneralizations(TypedTermList t, bool retrieveSubstitutions = true, void* extraData = nullptr) { NOT_IMPLEMENTED; }
  virtual TermQueryResultIterator getInstances(TypedTermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }

  virtual bool generalizationExists(TermList t) { NOT_IMPLEMENTED; }

  virtual void output(std::ostream& output) const = 0;

  friend std::ostream& operator<<(std::ostream& out, TermIndexingStructure const& self)
  { self.output(out); return out; }
};


};

#endif /* __TermIndexingStructure__ */
