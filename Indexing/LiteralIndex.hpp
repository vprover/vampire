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

#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Lib/Output.hpp"
#include "Lib/DHMap.hpp"

#include "Index.hpp"
#include "LiteralIndexingStructure.hpp"

namespace Indexing {

template<class Data>
class LiteralIndex
: public Index
{
public:
  VirtualIterator<LiteralClause> getAll()
  { return _is->getAll(); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LiteralClause>> getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions = true)
  { return _is->getUnifications(lit, complementary, retrieveSubstitutions); }

  VirtualIterator<QueryRes<AbstractingUnifier*, Data>> getUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa, bool fixedPointIteration)
  { return _is->getUwa(lit, complementary, uwa, fixedPointIteration); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LiteralClause>> getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions = true)
  { return _is->getGeneralizations(lit, complementary, retrieveSubstitutions); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LiteralClause>> getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions = true)
  { return _is->getInstances(lit, complementary, retrieveSubstitutions); }

  size_t getUnificationCount(Literal* lit, bool complementary)
  { return _is->getUnificationCount(lit, complementary); }

  friend std::ostream& operator<<(std::ostream& out,                 LiteralIndex const& self) { return out << *self._is; }
  friend std::ostream& operator<<(std::ostream& out, Output::Multiline<LiteralIndex>const& self) { return out << Output::multiline(*self.self._is, self.indent); }

protected:
  LiteralIndex() : _is(new LiteralSubstitutionTree<LiteralClause>()) {}

  void handle(Data data, bool add)
  { _is->handle(std::move(data), add); }

  std::unique_ptr<LiteralIndexingStructure<Data>> _is;
};

class BinaryResolutionIndex
: public LiteralIndex<LiteralClause>
{
public:
  BinaryResolutionIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class BackwardSubsumptionIndex
: public LiteralIndex<LiteralClause>
{
public:
  BackwardSubsumptionIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class FwSubsSimplifyingLiteralIndex
: public LiteralIndex<LiteralClause>
{
public:
  FwSubsSimplifyingLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class FSDLiteralIndex
: public LiteralIndex<LiteralClause>
{
public:
  FSDLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class UnitClauseLiteralIndex
: public LiteralIndex<LiteralClause>
{
public:
  UnitClauseLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class UnitClauseWithALLiteralIndex
: public LiteralIndex<LiteralClause>
{
  void handleClause(Clause* c, bool adding) override;
};

class NonUnitClauseLiteralIndex
: public LiteralIndex<LiteralClause>
{
  void handleClause(Clause* c, bool adding) override;
};

class NonUnitClauseWithALLiteralIndex
: public LiteralIndex<LiteralClause>
{
  void handleClause(Clause* c, bool adding) override;
};

class RewriteRuleIndex
: public LiteralIndex<LiteralClause>
{
public:
  RewriteRuleIndex(SaturationAlgorithm& salg);

  Clause* getCounterpart(Clause* c) {
    return _counterparts.get(c);
  }
protected:
  void handleClause(Clause* c, bool adding) override;
  Literal* getGreater(Clause* c);

private:
  void handleEquivalence(Clause* c, Literal* cgr, Clause* d, Literal* dgr, bool adding);

  LiteralSubstitutionTree<LiteralClause> _partialIndex;
  DHMap<Clause*,Clause*> _counterparts;
  Ordering& _ordering;
};

class UnitIntegerComparisonLiteralIndex
: public LiteralIndex<LiteralClause>
{
public:
  UnitIntegerComparisonLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

};

#endif /* __LiteralIndex__ */
