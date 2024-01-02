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

  SLQueryResultIterator getUnificationsWithConstraints(Literal* lit,
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

class BinaryResolutionIndex
: public LiteralIndex
{
public:
  BinaryResolutionIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class BackwardSubsumptionIndex
: public LiteralIndex
{
public:
  BackwardSubsumptionIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class FwSubsSimplifyingLiteralIndex
: public LiteralIndex
{
public:
  FwSubsSimplifyingLiteralIndex(LiteralIndexingStructure* is)
    : LiteralIndex(is)
  { }

protected:
  void handleClause(Clause* c, bool adding) override;
};

class FSDLiteralIndex
: public LiteralIndex
{
public:
  FSDLiteralIndex(LiteralIndexingStructure* is)
    : LiteralIndex(is)
  { }

protected:
  void handleClause(Clause* c, bool adding) override;
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

class UnitClauseWithALLiteralIndex
: public LiteralIndex
{
public:
  UnitClauseWithALLiteralIndex(LiteralIndexingStructure* is)
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

class NonUnitClauseWithALLiteralIndex
: public LiteralIndex
{
public:
  NonUnitClauseWithALLiteralIndex(LiteralIndexingStructure* is, bool selectedOnly=false)
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
  void addLiteral(Literal* c);
};

class UnitIntegerComparisonLiteralIndex
: public LiteralIndex
{
public:
  UnitIntegerComparisonLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {}

protected:
  void handleClause(Clause* c, bool adding);
};

};

#endif /* __LiteralIndex__ */
