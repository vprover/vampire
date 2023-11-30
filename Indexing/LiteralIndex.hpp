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
#include "LiteralIndexingStructure.hpp"


namespace Indexing {

class LiteralIndex
: public Index
{
public:
  USE_ALLOCATOR(LiteralIndex);

  virtual ~LiteralIndex();

  SLQueryResultIterator getAll();

  SLQueryResultIterator getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions = true)
  { return _is->getUnifications(lit, complementary, retrieveSubstitutions); }

  VirtualIterator<LQueryRes<AbstractingUnifier*>> getUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa, bool fixedPointIteration)
  { return _is->getUwa(lit, complementary, uwa, fixedPointIteration); }

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
  USE_ALLOCATOR(BinaryResolutionIndex);

  BinaryResolutionIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class BackwardSubsumptionIndex
: public LiteralIndex
{
public:
  USE_ALLOCATOR(BackwardSubsumptionIndex);

  BackwardSubsumptionIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class FwSubsSimplifyingLiteralIndex
: public LiteralIndex
{
public:
  USE_ALLOCATOR(FwSubsSimplifyingLiteralIndex);

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
  USE_ALLOCATOR(FSDLiteralIndex);

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
  USE_ALLOCATOR(UnitClauseLiteralIndex);

  UnitClauseLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class UnitClauseWithALLiteralIndex
: public LiteralIndex
{
public:
  USE_ALLOCATOR(UnitClauseWithALLiteralIndex);

  UnitClauseWithALLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class NonUnitClauseLiteralIndex
: public LiteralIndex
{
public:
  USE_ALLOCATOR(NonUnitClauseLiteralIndex);

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
  USE_ALLOCATOR(NonUnitClauseWithALLiteralIndex);

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
  USE_ALLOCATOR(RewriteRuleIndex);

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
  USE_ALLOCATOR(DismatchingLiteralIndex);

  DismatchingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
  void handleClause(Clause* c, bool adding);
  void addLiteral(Literal* c);
};

class UnitIntegerComparisonLiteralIndex
: public LiteralIndex
{
public:
  USE_ALLOCATOR(UnitIntegerComparisonLiteralIndex);

  UnitIntegerComparisonLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {}

protected:
  void handleClause(Clause* c, bool adding);
};

};

#endif /* __LiteralIndex__ */
