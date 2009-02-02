/**
 * @file TermIndex.hpp
 * Defines class TermIndex.
 */


#ifndef __TermIndex__
#define __TermIndex__

#include "Index.hpp"

namespace Indexing {

class TermIndex
: public Index
{
public:
  virtual ~TermIndex();

  TermQueryResultIterator getUnifications(TermList t,
	  bool retrieveSubstitutions = true);
  TermQueryResultIterator getGeneralizations(TermList t,
	  bool retrieveSubstitutions = true);
  TermQueryResultIterator getInstances(TermList t,
	  bool retrieveSubstitutions = true);

protected:
  TermIndex(TermIndexingStructure* is) : _is(is) {}

  TermIndexingStructure* _is;
};

class SuperpositionSubtermIndex
: public TermIndex
{
public:
  SuperpositionSubtermIndex(TermIndexingStructure* is)
  : TermIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class SuperpositionLHSIndex
: public TermIndex
{
public:
  SuperpositionLHSIndex(TermIndexingStructure* is)
  : TermIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class DemodulationSubtermIndex
: public TermIndex
{
public:
  DemodulationSubtermIndex(TermIndexingStructure* is)
  : TermIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class DemodulationLHSIndex
: public TermIndex
{
public:
  DemodulationLHSIndex(TermIndexingStructure* is)
  : TermIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

};
#endif /* __TermIndex__ */
