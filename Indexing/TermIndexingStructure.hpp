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
#include "Kernel/BottomUpEvaluation/TypedTermList.hpp"

namespace Indexing {

template<class Data>
class TermIndexingStructure {
  using TermQueryResultIterator = Indexing::TermQueryResultIterator<Data>;
public:
  virtual ~TermIndexingStructure() {}

  virtual void handle(Data data, bool insert) = 0;
  void insert(Data data) { handle(std::move(data), /* insert */ true ); }
  void remove(Data data) { handle(std::move(data), /* insert */ false); }

  virtual TermQueryResultIterator getUnifications(TermList t, bool retrieveSubstitutions = true, bool withConstraints = false) { NOT_IMPLEMENTED; }
  virtual TermQueryResultIterator getUnificationsUsingSorts(TypedTermList tt, bool retrieveSubstitutions = true, bool withConstraints = false) { NOT_IMPLEMENTED; }  
  virtual TermQueryResultIterator getGeneralizations(TermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual TermQueryResultIterator getInstances(TermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }

  virtual bool generalizationExists(TermList t) { NOT_IMPLEMENTED; }

};

};

#endif /* __TermIndexingStructure__ */
