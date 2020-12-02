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

#include "Kernel/Clause.hpp"
#include "Kernel/TermIterators.hpp"

#include <type_traits>

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
  TermQueryResultIterator getUnificationsWithConstraints(TermList t,
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

class SubVarSupSubtermIndex
: public TermIndex
{
public:
  CLASS_NAME(SubVarSupSubtermIndex);
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
  CLASS_NAME(SubVarSupLHSIndex);
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
  CLASS_NAME(NarrowingIndex);  
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
  CLASS_NAME(SkolemisingFormulaIndex);  
  USE_ALLOCATOR(SkolemisingFormulaIndex);
  
  SkolemisingFormulaIndex(TermIndexingStructure* is) : TermIndex(is)
  {}
  void insertFormula(TermList formula, TermList skolem);
};


class RenamingFormulaIndex
: public TermIndex
{
public:
  CLASS_NAME(RenamingFormulaIndex);  
  USE_ALLOCATOR(RenamingFormulaIndex);
  
  RenamingFormulaIndex(TermIndexingStructure* is) : TermIndex(is)
  {}
  void insertFormula(TermList formula, TermList name, Literal* lit, Clause* cls);
protected:
  void handleClause(Clause* c, bool adding);
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
  CLASS_NAME(DemodulationSubtermIndexImpl);
  USE_ALLOCATOR(DemodulationSubtermIndexImpl);

  DemodulationSubtermIndexImpl(TermIndexingStructure* is)
  : DemodulationSubtermIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding)
  {
    CALL("DemodulationSubtermIndex::handleClause");

    TimeCounter tc(TC_BACKWARD_DEMODULATION_INDEX_MAINTENANCE);

    static DHSet<TermList> inserted;

    unsigned cLen=c->length();
    for (unsigned i=0; i<cLen; i++) {
      // it is true (as stated below) that inserting only once per clause would be sufficient
      // however, vampire does not guarantee the order of literals stays the same in a clause (selected literals are moved to front)
      // so if the order changes while a clause is in the index (which can happen with "-sa otter")
      // the removes could be called on different literals than the inserts!
      inserted.reset();
      Literal* lit=(*c)[i];
      typename std::conditional<!combinatorySupSupport,
        NonVariableNonTypeIterator,
        FirstOrderSubtermIt>::type it(lit);
      while (it.hasNext()) {
        TermList t=it.next();
        if (!inserted.insert(t)) {//TODO existing error? Terms are inserted once per a literal
          //It is enough to insert a term only once per clause.
          //Also, once we know term was inserted, we know that all its
          //subterms were inserted as well, so we can skip them.
          it.right();
          continue;
        }
        if (adding) {
          _is->insert(t, lit, c);
        }
        else {
          _is->remove(t, lit, c);
        }
      }
    }
  }
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

};
#endif /* __TermIndex__ */
