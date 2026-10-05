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
#include "Lib/DHMap.hpp"

#include "Index.hpp"

namespace Indexing {

class NonGeneralizingLiteralIndex
: public Index
{
public:
  auto getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions = true)
  { return _is.getUnifications(lit, complementary, retrieveSubstitutions); }

  auto getUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa, bool fixedPointIteration)
  { return _is.getUwa(lit, complementary, uwa, fixedPointIteration); }

  template<bool higherOrder>
  auto getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions = true)
  {
    if constexpr (higherOrder) {
      // TODO(HOL): implement proper higher-order matching here
      // we override retrieveSubstitutions because we need the substitution for the aftercheck
      return pvi(iterTraits(_is.getInstances(lit, complementary, /*retrieveSubstitutions=*/true))
        .filter([lit](auto qr) {
          return iterTraits(VariableIterator(lit)).all([&qr](TermList var) {
            return !qr.unifier->applyToBoundQuery(var).containsLooseDBIndex();
          });
        }));
    } else {
      return _is.getInstances(lit, complementary, retrieveSubstitutions);
    }
  }

protected:
  void handle(LiteralClause data, bool add)
  { _is.handle(std::move(data), add); }

  LiteralSubstitutionTree<LiteralClause> _is;
};

class GeneralizingLiteralIndex
: public Index
{
public:
  auto getGeneralizations(Literal* lit, bool complementary) const
  { return _is.getGeneralizations(lit, complementary); }

protected:
  void handle(LiteralClause data, bool add)
  { _is.handle(std::move(data), add); }

  CodeTreeLIS<LiteralClause> _is;
};

class BinaryResolutionIndex
: public NonGeneralizingLiteralIndex
{
public:
  BinaryResolutionIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class BackwardSubsumptionIndex
: public NonGeneralizingLiteralIndex
{
public:
  BackwardSubsumptionIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class FwSubsSimplifyingLiteralIndex
: public GeneralizingLiteralIndex
{
public:
  FwSubsSimplifyingLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class FSDLiteralIndex
: public GeneralizingLiteralIndex
{
public:
  FSDLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

template<bool forGeneralizations>
class UnitClauseLiteralIndex
: public std::conditional_t<forGeneralizations, GeneralizingLiteralIndex, NonGeneralizingLiteralIndex>
{
public:
  UnitClauseLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class UnitClauseWithALLiteralIndex
: public NonGeneralizingLiteralIndex
{
public:
  UnitClauseWithALLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class NonUnitClauseLiteralIndex
: public NonGeneralizingLiteralIndex
{
public:
  NonUnitClauseLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class NonUnitClauseWithALLiteralIndex
: public NonGeneralizingLiteralIndex
{
public:
  NonUnitClauseWithALLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

class RewriteRuleIndex
: public GeneralizingLiteralIndex
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
  DHMap<unsigned,Clause*, FnvHash, IdentityHash> _counterparts;
  Ordering& _ordering;
};

class UnitIntegerComparisonLiteralIndex
: public NonGeneralizingLiteralIndex
{
public:
  UnitIntegerComparisonLiteralIndex(SaturationAlgorithm&) {}
protected:
  void handleClause(Clause* c, bool adding) override;
};

};

#endif /* __LiteralIndex__ */
