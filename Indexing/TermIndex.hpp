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
  void onAddedToContainer(Clause* c);
  void onRemovedFromContainer(Clause* c);
};

class SuperpositionLHSIndex
: public TermIndex
{
public:
  SuperpositionLHSIndex(TermIndexingStructure* is);
protected:
  void onAddedToContainer(Clause* c);
  void onRemovedFromContainer(Clause* c);
private:
  Ordering* _ord;
};

};
#endif /* __TermIndex__ */
