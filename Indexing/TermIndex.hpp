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
#include "TermSubstitutionTree.hpp"
#include "Lib/Set.hpp"

namespace Indexing {

class TermIndex
: public Index
{
public:
  USE_ALLOCATOR(TermIndex);

  virtual ~TermIndex();

  TermQueryResultIterator getUnifications(TypedTermList t, bool retrieveSubstitutions = true, bool withConstraints = false);
  TermQueryResultIterator getGeneralizations(TypedTermList t, bool retrieveSubstitutions = true);
  TermQueryResultIterator getInstances(TypedTermList t, bool retrieveSubstitutions = true);

protected:
  TermIndex(TermIndexingStructure* is) : _is(is) {}

  TermIndexingStructure* _is;
};

class SuperpositionSubtermIndex
: public TermIndex
{
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
: public TermIndex
{
public:
  USE_ALLOCATOR(SuperpositionLHSIndex);

  SuperpositionLHSIndex(TermSubstitutionTree* is, Ordering& ord, const Options& opt)
  : TermIndex(is), _ord(ord), _opt(opt), _tree(is) {};
protected:
  void handleClause(Clause* c, bool adding);
private:
  Ordering& _ord;
  const Options& _opt;
  TermSubstitutionTree* _tree;
};

/**
 * Term index for backward demodulation
 */
class DemodulationSubtermIndex
: public TermIndex
{
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
: public TermIndex
{
public:
  USE_ALLOCATOR(DemodulationLHSIndex);

  DemodulationLHSIndex(TermIndexingStructure* is, Ordering& ord, const Options& opt)
  : TermIndex(is), _ord(ord), _opt(opt), _insertionTimestamp(0) {};

  unsigned insertionTimestamp() const { return _insertionTimestamp; }
protected:
  void handleClause(Clause* c, bool adding);
private:
  Ordering& _ord;
  const Options& _opt;
  unsigned _insertionTimestamp;
};

/**
 * Term index for induction
 */
class InductionTermIndex
: public TermIndex
{
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
: public TermIndex
{
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
: public TermIndex
{
public:
  USE_ALLOCATOR(PrimitiveInstantiationIndex);

  PrimitiveInstantiationIndex(TermIndexingStructure* is) : TermIndex(is)
  {
    populateIndex();
  }
protected:
  void populateIndex();
};

class SubVarSupSubtermIndex
: public TermIndex
{
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
: public TermIndex
{
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
: public TermIndex
{
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
: public TermIndex
{
public:
  USE_ALLOCATOR(SkolemisingFormulaIndex);

  SkolemisingFormulaIndex(TermIndexingStructure* is) : TermIndex(is)
  {}
  void insertFormula(TermList formula, TermList skolem);
};

/*class HeuristicInstantiationIndex
: public TermIndex
{
public:
  USE_ALLOCATOR(HeuristicInstantiationIndex);

  HeuristicInstantiationIndex(TermIndexingStructure* is) : TermIndex(is)
  {}
protected:
  void insertInstantiation(TermList sort, TermList instantiation);
  void handleClause(Clause* c, bool adding);
private:
  Set<TermList> _insertedInstantiations;
};

class RenamingFormulaIndex
: public TermIndex
{
public:
  USE_ALLOCATOR(RenamingFormulaIndex);

  RenamingFormulaIndex(TermIndexingStructure* is) : TermIndex(is)
  {}
  void insertFormula(TermList formula, TermList name, Literal* lit, Clause* cls);
protected:
  void handleClause(Clause* c, bool adding);
};*/

};
#endif /* __TermIndex__ */
