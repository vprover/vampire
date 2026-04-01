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
#include "IndexingStructure.hpp"

namespace Indexing {

template<class Data>
class TermIndexingStructure : public IndexingStructure<Data> {
public:
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getUnifications(TypedTermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<QueryRes<AbstractingUnifier*, Data>> getUwa(TypedTermList t, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) = 0;
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getGeneralizations(TypedTermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getInstances(TypedTermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
};


};

#endif /* __TermIndexingStructure__ */
