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
 * @file TermIndex.hpp
 * Defines class TermIndex.
 */


#ifndef __TermIndex__
#define __TermIndex__

#include "Index.hpp"
#include "TermIndexingStructure.hpp"

namespace Indexing {

template<class Data>
class TermIndex
: public Index
{
public:
  ~TermIndex() override {}

  VirtualIterator<QueryRes<AbstractingUnifier*, Data>> getUwa(TypedTermList t, Options::UnificationWithAbstraction uwa, bool fixedPointIteration)
  { return _is->getUwa(t, uwa, fixedPointIteration); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getUnifications(TypedTermList t, bool retrieveSubstitutions = true)
  { return _is->getUnifications(t, retrieveSubstitutions); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getGeneralizations(TypedTermList t, bool retrieveSubstitutions = true)
  { return _is->getGeneralizations(t, retrieveSubstitutions); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getInstances(TypedTermList t, bool retrieveSubstitutions = true)
  { return _is->getInstances(t, retrieveSubstitutions); }

  friend std::ostream& operator<<(std::ostream& out, TermIndex const& self)
  { return out << *self._is; }
protected:
  TermIndex(TermIndexingStructure<Data>* is) : _is(is) {}

  std::unique_ptr<TermIndexingStructure<Data>> _is;
};

class SuperpositionSubtermIndex
: public TermIndex<TermLiteralClause>
{
public:
  SuperpositionSubtermIndex(SaturationAlgorithm& salg);
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  Ordering& _ord;
};

class SuperpositionLHSIndex
: public TermIndex<TermLiteralClause>
{
public:
  SuperpositionLHSIndex(SaturationAlgorithm& salg);
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  Ordering& _ord;
  const Options& _opt;
};

/**
 * Term index for backward demodulation
 */
class DemodulationSubtermIndex
: public TermIndex<TermLiteralClause>
{
public:
  DemodulationSubtermIndex(SaturationAlgorithm& salg);
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  const bool _skipNonequationalLiterals;
};

/**
 * Term index for forward demodulation
 */
class DemodulationLHSIndex
: public TermIndex<DemodulatorData>
{
public:
  DemodulationLHSIndex(SaturationAlgorithm& salg);
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  Ordering& _ord;
  const bool _preordered;
};

/**
 * Term index for induction
 */
class InductionTermIndex
: public TermIndex<TermLiteralClause>
{
public:
  InductionTermIndex(SaturationAlgorithm& salg);
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  const bool _inductionGroundOnly;
};

/**
 * Term index for structural induction
 */
class StructInductionTermIndex
: public TermIndex<TermLiteralClause>
{
public:
  StructInductionTermIndex(SaturationAlgorithm& salg);
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  const bool _inductionGroundOnly;
};

class SkolemisingFormulaIndex
: public TermIndex<TermWithValue<TermList>>
{
public:
  SkolemisingFormulaIndex(SaturationAlgorithm&);
  void insertFormula(TermList formula, TermList skolem);
};

} // namespace Indexing
#endif /* __TermIndex__ */
