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

#include "Indexing/TermSubstitutionTree.hpp"
#include "TermIndexingStructure.hpp"
#include "Lib/Set.hpp"

namespace Indexing {

template<class Data>
class TermIndex
: public Index
{
  using TermIndexingStructure   = Indexing::TermIndexingStructure<Data>;
public:
  USE_ALLOCATOR(TermIndex);

  virtual ~TermIndex() {}


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
  TermIndex(TermIndexingStructure* is) : _is(is) {}

  std::unique_ptr<TermIndexingStructure> _is;
};

class SuperpositionSubtermIndex
: public TermIndex<TermLiteralClause>
{
  using TermIndex             = Indexing::TermIndex<TermLiteralClause>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<TermLiteralClause>;
public:
  USE_ALLOCATOR(SuperpositionSubtermIndex);

  SuperpositionSubtermIndex(TermIndexingStructure* is, Ordering& ord)
  : TermIndex(is), _ord(ord) {};
protected:
  void handleClause(Clause* c, bool adding);
private:
  Ordering& _ord;
};

class SuperpositionLHSIndex
: public TermIndex<TermLiteralClause>
{
  using TermIndex             = Indexing::TermIndex<TermLiteralClause>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<TermLiteralClause>;
public:
  USE_ALLOCATOR(SuperpositionLHSIndex);

  SuperpositionLHSIndex(TermSubstitutionTree<TermLiteralClause>* is, Ordering& ord, const Options& opt)
  : TermIndex(is), _ord(ord), _opt(opt), _tree(is) {};
protected:
  void handleClause(Clause* c, bool adding);
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
  using TermIndex             = Indexing::TermIndex<TermLiteralClause>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<TermLiteralClause>;
public:
  // people seemed to like the class, although it add's no interface on top of TermIndex
  DemodulationSubtermIndex(TermIndexingStructure* is)
  : TermIndex(is) {};
protected:
  // it's the implementation of this below in DemodulationSubtermIndexImpl, which makes this work
  void handleClause(Clause* c, bool adding) = 0;
};

template <bool combinatorySupSupport>
class DemodulationSubtermIndexImpl
: public DemodulationSubtermIndex
{
  using TermIndex             = Indexing::TermIndex<TermLiteralClause>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<TermLiteralClause>;
public:
  USE_ALLOCATOR(DemodulationSubtermIndexImpl);

  DemodulationSubtermIndexImpl(TermIndexingStructure* is)
  : DemodulationSubtermIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

/**
 * Term index for forward demodulation
 */
class DemodulationLHSIndex
: public TermIndex<TermLiteralClause>
{
  using TermIndex             = Indexing::TermIndex<TermLiteralClause>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<TermLiteralClause>;
public:
  USE_ALLOCATOR(DemodulationLHSIndex);

  DemodulationLHSIndex(TermIndexingStructure* is, Ordering& ord, const Options& opt)
  : TermIndex(is), _ord(ord), _opt(opt) {};
protected:
  void handleClause(Clause* c, bool adding);
private:
  Ordering& _ord;
  const Options& _opt;
};

/**
 * Term index for induction
 */
class InductionTermIndex
: public TermIndex<TermLiteralClause>
{
  using TermIndex             = Indexing::TermIndex<TermLiteralClause>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<TermLiteralClause>;
public:
  USE_ALLOCATOR(InductionTermIndex);

  InductionTermIndex(TermIndexingStructure* is)
  : TermIndex(is) {}

protected:
  void handleClause(Clause* c, bool adding);
};

/**
 * Term index for structural induction
 */
class StructInductionTermIndex
: public TermIndex<TermLiteralClause>
{
  using TermIndex             = Indexing::TermIndex<TermLiteralClause>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<TermLiteralClause>;
public:
  USE_ALLOCATOR(StructInductionTermIndex);

  StructInductionTermIndex(TermIndexingStructure* is)
  : TermIndex(is) {}

protected:
  void handleClause(Clause* c, bool adding);
};

/////////////////////////////////////////////////////
// Indices for higher-order inferences from here on//
/////////////////////////////////////////////////////

class PrimitiveInstantiationIndex
: public TermIndex<TermWithoutValue>
{
public:
  USE_ALLOCATOR(PrimitiveInstantiationIndex);

  PrimitiveInstantiationIndex(Indexing::TermIndexingStructure<TermWithoutValue>* is) : TermIndex(is)
  {
    populateIndex();
  }
protected:
  void populateIndex();
};

class SubVarSupSubtermIndex
: public TermIndex<TermLiteralClause>
{
  using TermIndex             = Indexing::TermIndex<TermLiteralClause>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<TermLiteralClause>;
public:
  USE_ALLOCATOR(SubVarSupSubtermIndex);

  SubVarSupSubtermIndex(TermIndexingStructure* is, Ordering& ord)
  : TermIndex(is), _ord(ord) {};
protected:
  void handleClause(Clause* c, bool adding);
private:
  Ordering& _ord;
};

class SubVarSupLHSIndex
: public TermIndex<TermLiteralClause>
{
  using TermIndex             = Indexing::TermIndex<TermLiteralClause>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<TermLiteralClause>;
public:
  USE_ALLOCATOR(SubVarSupLHSIndex);

  SubVarSupLHSIndex(TermIndexingStructure* is, Ordering& ord, const Options& opt)
  : TermIndex(is), _ord(ord) {};
protected:
  void handleClause(Clause* c, bool adding);
private:
  Ordering& _ord;
};

/**
 * Index used for narrowing with combinator axioms
 */
class NarrowingIndex
: public TermIndex<TermLiteralClause>
{
  using TermIndex             = Indexing::TermIndex<TermLiteralClause>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<TermLiteralClause>;
public:
  USE_ALLOCATOR(NarrowingIndex);

  NarrowingIndex(TermIndexingStructure* is) : TermIndex(is)
  {
    populateIndex();
  }
protected:
  void populateIndex();
};

class SkolemisingFormulaIndex
: public TermIndex<TermWithValue<TermList>>
{
  using LeafData = TermWithValue<TermList>;
  using TermIndex             = Indexing::TermIndex<LeafData>;
  using TermIndexingStructure = Indexing::TermIndexingStructure<LeafData>;
public:
  USE_ALLOCATOR(SkolemisingFormulaIndex);

  SkolemisingFormulaIndex(TermIndexingStructure* is) : TermIndex(is)
  {}
  void insertFormula(TermList formula, TermList skolem);
};

} // namespace TermIndex

#endif /* __TermIndex__ */
