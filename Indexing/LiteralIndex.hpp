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

#include "Indexing/CodeTreeInterfaces.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Lib/Output.hpp"
#include "Lib/DHMap.hpp"

#include "Index.hpp"
#include "LiteralIndexingStructure.hpp"

namespace Indexing {

template<class Data, bool forGeneralizations>
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

  friend std::ostream& operator<<(std::ostream& out,                 LiteralIndex const& self) { return out << *self._is; }
  friend std::ostream& operator<<(std::ostream& out, Output::Multiline<LiteralIndex>const& self) { return out << Output::multiline(*self.self._is, self.indent); }

protected:
  LiteralIndex() : _is(new std::conditional_t<forGeneralizations, CodeTreeLIS<LiteralClause>, LiteralSubstitutionTree<LiteralClause>>()) {}

  void handle(Data data, bool add)
  { _is->handle(std::move(data), add); }

  std::unique_ptr<LiteralIndexingStructure<Data>> _is;
};

class BinaryResolutionIndex
: public LiteralIndex<LiteralClause, false>
{
public:
  BinaryResolutionIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class BackwardSubsumptionIndex
: public LiteralIndex<LiteralClause, false>
{
public:
  BackwardSubsumptionIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class FwSubsSimplifyingLiteralIndex
: public LiteralIndex<LiteralClause, true>
{
public:
  FwSubsSimplifyingLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class FSDLiteralIndex
: public LiteralIndex<LiteralClause, true>
{
public:
  FSDLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

template<bool forGeneralizations>
class UnitClauseLiteralIndex
: public LiteralIndex<LiteralClause, forGeneralizations>
{
public:
  UnitClauseLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class UnitClauseWithALLiteralIndex
: public LiteralIndex<LiteralClause, false>
{
public:
  UnitClauseWithALLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class NonUnitClauseLiteralIndex
: public LiteralIndex<LiteralClause, false>
{
public:
  NonUnitClauseLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class NonUnitClauseWithALLiteralIndex
: public LiteralIndex<LiteralClause, false>
{
public:
  NonUnitClauseWithALLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class RewriteRuleIndex
: public LiteralIndex<LiteralClause, true>
{
public:
  RewriteRuleIndex(SaturationAlgorithm& salg);

  Clause* getCounterpart(Clause* c) {
    return _counterparts.get(c->number());
  }
protected:
  void handleClause(Clause* c, bool adding) override;
  Literal* getGreater(Clause* c);

private:
  void handleEquivalence(Clause* c, Literal* cgr, Clause* d, Literal* dgr, bool adding);

  LiteralSubstitutionTree<LiteralClause> _partialIndex;
  DHMap<unsigned,Clause*> _counterparts;
  Ordering& _ordering;
};

class UnitIntegerComparisonLiteralIndex
: public LiteralIndex<LiteralClause, false>
{
public:
  UnitIntegerComparisonLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

};

#endif /* __LiteralIndex__ */
