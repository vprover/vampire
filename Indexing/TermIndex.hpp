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
  virtual ~TermIndex();

  TermQueryResultIterator getUnifications(TypedTermList t, bool retrieveSubstitutions = true, bool withConstraints = false);
  TermQueryResultIterator getGeneralizations(TypedTermList t, bool retrieveSubstitutions = true, void* extra = nullptr);
  TermQueryResultIterator getInstances(TypedTermList t, bool retrieveSubstitutions = true);

protected:
  TermIndex(TermIndexingStructure* is) : _is(is) {}

  TermIndexingStructure* _is;
};

class SuperpositionSubtermIndex
: public TermIndex
{
public:
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

/**
 * Term index for backward demodulation
 */
class BlockedTermIndex
: public TermIndex
{
public:
  BlockedTermIndex(TermIndexingStructure* is)
  : TermIndex(is) {}

protected:
  void handleClause(Clause* c, bool adding);
};

template <bool combinatorySupSupport>
class DemodulationSubtermIndexImpl
: public DemodulationSubtermIndex
{
public:
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
  DemodulationLHSIndex(TermIndexingStructure* is, const Ordering& ord, const Options& opt, SaturationAlgorithm* salg)
  : TermIndex(is), _ord(ord), _opt(opt), _salg(salg) {};
protected:
  void handleClause(Clause* c, bool adding);
private:
  const Ordering& _ord;
  const Options& _opt;
  SaturationAlgorithm* _salg;
};

/**
 * Term index for induction
 */
class InductionTermIndex
: public TermIndex
{
public:
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
  SkolemisingFormulaIndex(TermIndexingStructure* is) : TermIndex(is)
  {}
  void insertFormula(TermList formula, TermList skolem);
};

/*class HeuristicInstantiationIndex
: public TermIndex
{
public:
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
  RenamingFormulaIndex(TermIndexingStructure* is) : TermIndex(is)
  {}
  void insertFormula(TermList formula, TermList name, Literal* lit, Clause* cls);
protected:
  void handleClause(Clause* c, bool adding);
};*/

};
#endif /* __TermIndex__ */
