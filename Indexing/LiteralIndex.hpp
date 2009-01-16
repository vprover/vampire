/**
 * @file LiteralIndex.hpp
 * Defines class LiteralIndex.
 */


#ifndef __LiteralIndex__
#define __LiteralIndex__

#include "Index.hpp"

namespace Indexing {

class LiteralIndex
: public Index
{
public:
  virtual ~LiteralIndex();

  SLQueryResultIterator getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true);

  SLQueryResultIterator getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true);

  SLQueryResultIterator getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions = true);

protected:
  LiteralIndex(LiteralIndexingStructure* is) : _is(is) {}

  LiteralIndexingStructure* _is;
};

class GeneratingLiteralIndex
: public LiteralIndex
{
public:
  GeneratingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void onAddedToContainer(Clause* c);
  void onRemovedFromContainer(Clause* c);
};

class SimplifyingLiteralIndex
: public LiteralIndex
{
public:
  SimplifyingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void onAddedToContainer(Clause* c);
  void onRemovedFromContainer(Clause* c);
};

class AtomicClauseSimplifyingLiteralIndex
: public LiteralIndex
{
public:
  AtomicClauseSimplifyingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void onAddedToContainer(Clause* c);
  void onRemovedFromContainer(Clause* c);
};


};

#endif /* __LiteralIndex__ */
