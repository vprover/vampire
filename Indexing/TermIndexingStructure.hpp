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
#include "Kernel/TypedTermList.hpp"
#include "Kernel/MismatchHandler.hpp"

namespace Indexing {

template<class Data>
class TermIndexingStructure {
public:
  virtual ~TermIndexingStructure() {}

  virtual void handle(Data data, bool insert) = 0;
  void insert(Data data) { handle(std::move(data), /* insert */ true ); }
  void remove(Data data) { handle(std::move(data), /* insert */ false); }

  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getUnifications(TermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<QueryRes<AbstractingUnifier*, Data>> getUwa(TypedTermList t, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) = 0;
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getUnificationsUsingSorts(TypedTermList tt, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }  
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getGeneralizations(TermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getInstances(TermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }

  virtual bool generalizationExists(TermList t) { NOT_IMPLEMENTED; }

  virtual void output(std::ostream& output) const = 0;
  friend std::ostream& operator<<(std::ostream& out, TermIndexingStructure const& self)
  { self.output(out); return out; }
};


};

#endif /* __TermIndexingStructure__ */
