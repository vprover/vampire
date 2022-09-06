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
#include "Lib/Set.hpp"

namespace Indexing {

class TermIndex
: public Index
{
public:
  CLASS_NAME(TermIndex);
  USE_ALLOCATOR(TermIndex);

  virtual ~TermIndex();

  TermQueryResultIterator getUnifications(TermList t,
	  bool retrieveSubstitutions = true);
  TermQueryResultIterator getUnificationsUsingSorts(TermList t, TermList sort,
    bool retrieveSubstitutions = true);
  TermQueryResultIterator getGeneralizations(TermList t,
	  bool retrieveSubstitutions = true);
  TermQueryResultIterator getInstances(TermList t,
	  bool retrieveSubstitutions = true);

protected:
  TermIndex(TermIndexingStructure* is) : _is(is) {}

  TermIndexingStructure* _is;
};

class SuperpositionSubtermIndex
: public TermIndex
{
public:
  CLASS_NAME(SuperpositionSubtermIndex);
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
  CLASS_NAME(SuperpositionLHSIndex);
  USE_ALLOCATOR(SuperpositionLHSIndex);

  SuperpositionLHSIndex(TermIndexingStructure* is, Ordering& ord, const Options& opt)
  : TermIndex(is), _ord(ord), _opt(opt) {};
protected:
  void handleClause(Clause* c, bool adding);
private:
  Ordering& _ord;
  const Options& _opt;
};

/**
 * Term index for backward demodulation
 */
template <class SubtermIterator>
class DemodulationSubtermIndex
: public TermIndex
{
public:
  CLASS_NAME(DemodulationSubtermIndex);
  USE_ALLOCATOR(DemodulationSubtermIndex);

  DemodulationSubtermIndex(TermIndexingStructure* is)
  : TermIndex(is) {};
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
  CLASS_NAME(DemodulationLHSIndex);
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
: public TermIndex
{
public:
  CLASS_NAME(InductionTermIndex);
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
  CLASS_NAME(StructInductionTermIndex);
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
  CLASS_NAME(PrimitiveInstantiationIndex);
  USE_ALLOCATOR(PrimitiveInstantiationIndex);

  PrimitiveInstantiationIndex(TermIndexingStructure* is) : TermIndex(is)
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
  CLASS_NAME(SkolemisingFormulaIndex);
  USE_ALLOCATOR(SkolemisingFormulaIndex);

  SkolemisingFormulaIndex(TermIndexingStructure* is) : TermIndex(is)
  {}
  void insertFormula(TermList formula, TermList skolem);
};

/*class HeuristicInstantiationIndex
: public TermIndex
{
public:
  CLASS_NAME(HeuristicInstantiationIndex);
  USE_ALLOCATOR(HeuristicInstantiationIndex);

  HeuristicInstantiationIndex(TermIndexingStructure* is) : TermIndex(is)
  {}
protected:
  void insertInstantiation(TermList sort, TermList instantiation);
  void handleClause(Clause* c, bool adding);
private:
  Set<TermList> _insertedInstantiations;
};*/

};
#endif /* __TermIndex__ */
