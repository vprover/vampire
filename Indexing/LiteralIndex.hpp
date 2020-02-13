
/*
 * File LiteralIndex.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
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
  CLASS_NAME(LiteralIndex);
  USE_ALLOCATOR(LiteralIndex);

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

class GeneratingLiteralIndex
: public LiteralIndex
{
public:
  CLASS_NAME(GeneratingLiteralIndex);
  USE_ALLOCATOR(GeneratingLiteralIndex);

  GeneratingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class SimplifyingLiteralIndex
: public LiteralIndex
{
public:
  CLASS_NAME(SimplifyingLiteralIndex);
  USE_ALLOCATOR(SimplifyingLiteralIndex);

  SimplifyingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class FwSubsSimplifyingLiteralIndex
: public LiteralIndex
{
public:
  CLASS_NAME(FwSubsSimplifyingLiteralIndex);
  USE_ALLOCATOR(FwSubsSimplifyingLiteralIndex);

  FwSubsSimplifyingLiteralIndex(LiteralIndexingStructure* is)
    : LiteralIndex(is)
  { }

protected:
  void handleClause(Clause* c, bool adding) override;
};

class FSDSimplifyingLiteralIndex
: public LiteralIndex
{
public:
  CLASS_NAME(FSDSimplifyingLiteralIndex);
  USE_ALLOCATOR(FSDSimplifyingLiteralIndex);

  FSDSimplifyingLiteralIndex(LiteralIndexingStructure* is)
    : LiteralIndex(is)
  { }

protected:
  void handleClause(Clause* c, bool adding) override;
};

class UnitClauseLiteralIndex
: public LiteralIndex
{
public:
  CLASS_NAME(UnitClauseLiteralIndex);
  USE_ALLOCATOR(UnitClauseLiteralIndex);

  UnitClauseLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class NonUnitClauseLiteralIndex
: public LiteralIndex
{
public:
  CLASS_NAME(NonUnitClauseLiteralIndex);
  USE_ALLOCATOR(NonUnitClauseLiteralIndex);

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
  CLASS_NAME(RewriteRuleIndex);
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
  CLASS_NAME(DismatchingLiteralIndex);
  USE_ALLOCATOR(DismatchingLiteralIndex);

  DismatchingLiteralIndex(LiteralIndexingStructure* is)
  : LiteralIndex(is) {};
  void handleClause(Clause* c, bool adding);
  void addLiteral(Literal* c);
};

};

#endif /* __LiteralIndex__ */
