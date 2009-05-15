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

  SLQueryResultIterator getAll();

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
  void handleClause(Clause* c, bool adding);
};

class SimplifyingLiteralIndex
: public LiteralIndex
{
public:
  SimplifyingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class FwSubsSimplifyingLiteralIndex
: public LiteralIndex
{
public:
  FwSubsSimplifyingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class UnitClauseSimplifyingLiteralIndex
: public LiteralIndex
{
public:
  UnitClauseSimplifyingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};


};

#endif /* __LiteralIndex__ */
