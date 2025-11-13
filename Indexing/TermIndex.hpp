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

#include "Indexing/TermSubstitutionTree.hpp"
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
  SuperpositionSubtermIndex(Indexing::TermIndexingStructure<TermLiteralClause>* is, Ordering& ord)
  : TermIndex(is), _ord(ord) {};
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  Ordering& _ord;
};

class SuperpositionLHSIndex
: public TermIndex<TermLiteralClause>
{
public:
  SuperpositionLHSIndex(TermSubstitutionTree<TermLiteralClause>* is, Ordering& ord, const Options& opt)
  : TermIndex(is), _ord(ord), _opt(opt), _tree(is) {};
protected:
  void handleClause(Clause* c, bool adding) override;
private:
  Ordering& _ord;
  const Options& _opt;
  TermSubstitutionTree<TermLiteralClause>* _tree;
};

/**
 * Term index for backward demodulation
 */
class DemodulationSubtermIndex
: public TermIndex<TermLiteralClause>
{
public:
  DemodulationSubtermIndex(TermIndexingStructure<TermLiteralClause>* is, const Options& opt)
  : TermIndex(is), _skipNonequationalLiterals(opt.demodulationOnlyEquational()) {};
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
  DemodulationLHSIndex(TermIndexingStructure<DemodulatorData>* is, Ordering& ord, const Options& opt)
  : TermIndex(is), _ord(ord), _preordered(opt.forwardDemodulation()==Options::Demodulation::PREORDERED) {};
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
  InductionTermIndex(TermIndexingStructure<TermLiteralClause>* is, const Options& opt)
  : TermIndex(is), _inductionGroundOnly(opt.inductionGroundOnly()) {}

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
  StructInductionTermIndex(TermIndexingStructure<TermLiteralClause>* is, const Options& opt)
  : TermIndex(is), _inductionGroundOnly(opt.inductionGroundOnly()) {}

protected:
  void handleClause(Clause* c, bool adding) override;
private:
  const bool _inductionGroundOnly;
};

class SkolemisingFormulaIndex
: public TermIndex<TermWithValue<TermList>>
{
public:
  SkolemisingFormulaIndex(TermIndexingStructure<TermWithValue<TermList>>* is) : TermIndex(is)
  {}
  void insertFormula(TermList formula, TermList skolem);
};

} // namespace Indexing
#endif /* __TermIndex__ */
