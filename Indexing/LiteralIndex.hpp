/**
 * @file LiteralIndex.hpp
 * Defines class LiteralIndex.
 */


#ifndef __LiteralIndex__
#define __LiteralIndex__

#include "Lib/DHMap.hpp"

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

  size_t getUnificationCount(Literal* lit, bool complementary);


protected:
  LiteralIndex(LiteralIndexingStructure* is) : _is(is) {}

  void handleLiteral(Literal* lit, Clause* cl, bool add);

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

class UnitClauseLiteralIndex
: public LiteralIndex
{
public:
  UnitClauseLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class NonUnitClauseLiteralIndex
: public LiteralIndex
{
public:
  NonUnitClauseLiteralIndex(LiteralIndexingStructure* is, bool selectedOnly=false)
  : LiteralIndex(is), _selectedOnly(selectedOnly) {};
protected:
  void handleClause(Clause* c, bool adding);
private:
  bool _selectedOnly;
};

class RewriteRuleIndex
: public LiteralIndex
{
public:
  RewriteRuleIndex(LiteralIndexingStructure* is, Ordering& ordering);
  ~RewriteRuleIndex();

  Clause* getCounterpart(Clause* c) {
    return _counterparts.get(c);
  }
protected:
  void handleClause(Clause* c, bool adding);
  Literal* getGreater(Clause* c);

private:
  void handleEquivalence(Clause* c, Literal* cgr, Clause* d, Literal* dgr, bool adding);

  LiteralIndexingStructure* _partialIndex;
  DHMap<Clause*,Clause*> _counterparts;
  Ordering& _ordering;
};

class DismatchingLiteralIndex
: public LiteralIndex
{
public:
  DismatchingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
  void handleClause(Clause* c, bool adding);
};

};

#endif /* __LiteralIndex__ */
