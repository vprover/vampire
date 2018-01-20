
/*
 * File TermAlgebraIndex.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file AcyclicityIndex.hpp
 * Defines class AcyclicityIndex
 */

#ifndef __AcyclicityIndex__
#define __AcyclicityIndex__

#include "Indexing/Index.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/TermIndex.hpp"
#include "Indexing/TermIndexingStructure.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/List.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Forwards.hpp"

namespace Indexing {

struct ChainQueryResult {
  ChainQueryResult(Lib::List<Kernel::Literal*>* l,
                   Lib::List<Kernel::Clause*>* p,
                   Lib::List<Kernel::Clause*>* c,
                   TermList t1,
                   unsigned t1sort,
                   TermList tn,
                   unsigned tnsort)
    :
    literals(l),
    premises(p),
    clausesTheta(c),
    term1(t1),
    term1sort(t1sort),
    termn(tn),
    termnsort(tnsort),
    isCycle(false)
  {}

  ChainQueryResult(Lib::List<Kernel::Literal*>* l,
                   Lib::List<Kernel::Clause*>* p,
                   Lib::List<Kernel::Clause*>* c)
    :
    literals(l),
    premises(p),
    clausesTheta(c),
    term1(),
    term1sort(0),
    termn(),
    termnsort(0),
    isCycle(true)
  {}

  CLASS_NAME(ChainQueryResult);
  USE_ALLOCATOR(ChainQueryResult);

  unsigned totalLengthClauses();
  
  Lib::List<Kernel::Literal*>* literals;
  Lib::List<Kernel::Clause*>* premises;
  Lib::List<Kernel::Clause*>* clausesTheta; // the three lists should be the same length
  Kernel::TermList term1;
  unsigned term1sort;
  Kernel::TermList termn; // null if chain is a cycle
  unsigned termnsort;
  bool isCycle;
};

class AcyclicityIndex
: public Index
{
public:
  AcyclicityIndex(Indexing::TermIndexingStructure* tis, Ordering& ord) :
    _lIndex(),
    _tis(tis),
    _ord(ord)
  {}

  ~AcyclicityIndex() {}
  
  void insert(Kernel::Literal *lit, Kernel::Clause *c);
  void remove(Kernel::Literal *lit, Kernel::Clause *c);

  Lib::VirtualIterator<ChainQueryResult> queryChains(Kernel::Literal *lit, Kernel::Clause *c);
             
  CLASS_NAME(AcyclicityIndex);
  USE_ALLOCATOR(AcyclicityIndex);
protected:
  void handleClause(Kernel::Clause* c, bool adding);
private:
  bool matchesPattern(Kernel::Literal *lit, Kernel::TermList *&fs, Kernel::TermList *&t, unsigned *sort);
  Lib::List<TermList>* getSubterms(Kernel::Term *t);
  
  struct IndexEntry;
  struct ChainSearchTreeNode;
  struct ChainSearchIterator;
  typedef pair<Kernel::Literal*, Kernel::Clause*> ULit;
  typedef Lib::DHMap<ULit, IndexEntry*> LIndex;

  LIndex _lIndex;
  Indexing::TermIndexingStructure* _tis;
  Ordering& _ord;
};

class TARulesRHSIndex
: public TermIndex
{
public:
  CLASS_NAME(TARulesRHSIndex);
  USE_ALLOCATOR(TARulesRHSIndex);

  TARulesRHSIndex(TermIndexingStructure* is, Ordering& ord)
    : TermIndex(is), _ord(ord)
  {};

  static bool rhsEligible(Literal* lit, const Ordering& ord, TermList*& lhs, TermList*& rhs);
  
protected:
  void handleClause(Clause* c, bool adding);
private:
  Ordering& _ord;
};

}

#endif
