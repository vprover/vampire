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

  virtual void insert(TermList t, Literal* lit, Clause* cls) = 0;
  virtual void remove(TermList t, Literal* lit, Clause* cls) = 0;

  virtual TermQueryResultIterator getUnifications(TermList t,
	  bool retrieveSubstitutions = true) = 0;
  virtual TermQueryResultIterator getGeneralizations(TermList t,
	  bool retrieveSubstitutions = true) = 0;
  virtual TermQueryResultIterator getInstances(TermList t,
	  bool retrieveSubstitutions = true) = 0;
};

};

#endif /* __TermIndexingStructure__ */
