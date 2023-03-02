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
 * @file DelayedUnification.hpp
 * Things for Ahmed/Johannes' delayed-unification CADE '23 calculus
 */

#ifndef __DelayedUnification__
#define __DelayedUnification__

#include "Debug/Assertion.hpp"
#include "Kernel/Clause.hpp"
#include "Indexing/Index.hpp"
#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

// base class for delayed unification "indices"
template<typename T>
class TopSymbolIndex: public Indexing::Index {
public:
  CLASS_NAME(TopSymbolIndex)
  USE_ALLOCATOR(TopSymbolIndex)

  struct Entry {
    Clause *clause;
    Literal *literal;
    T term;

    bool operator==(const Entry &other) const {
      return clause == other.clause && literal == other.literal && term == other.term;
    }

    bool operator!=(const Entry &other) const {
      return !operator==(other);
    }

    unsigned defaultHash() const {
      return HashUtils::combine(
        DefaultHash::hash(clause),
        DefaultHash::hash(literal),
        DefaultHash::hash(term)
      );
    }

    unsigned defaultHash2() const {
      return HashUtils::combine(
        DefaultHash2::hash(clause),
        DefaultHash2::hash(literal),
        DefaultHash2::hash(term)
      );
    }
  };

  ~TopSymbolIndex() {
    CALL("~TopSymbolIndex")
    typename decltype(_functors)::Iterator it(_functors);
    while(it.hasNext())
      delete it.next();
  }

  void handle(Clause *c, Literal *l, T t, bool adding) {
    CALL("TopSymbolIndex::handle")
    typedef DHSet<Entry> Entries;

    Entries **entriesPtr;
    _functors.getValuePtr(t->functor(), entriesPtr, nullptr);
    if(!*entriesPtr)
      *entriesPtr = new Entries();
    Entries *entries = *entriesPtr;

    if(adding)
      entries->insert({c, l, t});
    else
      entries->remove({c, l, t});
  }

  VirtualIterator<Entry> entries() {
    return pvi(getMapAndFlattenIterator(
      _functors.range(),
      [](DHSet<Entry> *entries) { return entries->iterator(); }
    ));
  }

  VirtualIterator<Entry> query(unsigned functor) {
    CALL("TopSymbolIndex::query")
    DHSet<Entry> *entries;
    if(!_functors.find(functor, entries))
      return VirtualIterator<Entry>::getEmpty();
    return entries->iterator();
  }

private:
  // map from functors to a set of clause/literal pairs
  // TODO DHSet doesn't have a move constructor so it has to be heap-allocated
  // Johannes has already fixed this in the substitution-tree refactor, drop the indirection when we can
  DHMap<unsigned, DHSet<Entry> *> _functors;
};

// non-variable subterms of selected literals
class DelayedSubterms: public TopSymbolIndex<Term *> {
public:
  CLASS_NAME(DelayedSubterms);
  USE_ALLOCATOR(DelayedSubterms);

  DelayedSubterms(const Ordering &ordering) : _ordering(ordering) {}
  void handleClause(Kernel::Clause* c, bool adding) override;

private:
  // current ordering
  const Ordering& _ordering;
};

// left-hand-sides of selected positive equations
class DelayedLHS: public TopSymbolIndex<Term *> {
public:
  CLASS_NAME(DelayedLHS);
  USE_ALLOCATOR(DelayedLHS);

  DelayedLHS(const Ordering &ordering, const Options &options) : _ordering(ordering), _options(options) {}
  void handleClause(Kernel::Clause* c, bool adding) override;
  // variable left-hand-sides
  DHSet<TopSymbolIndex<TermList>::Entry>::Iterator variables() {
    return decltype(_variables)::Iterator(_variables);
  }

private:
  // current ordering
  const Ordering& _ordering;
  // current options
  const Options &_options;

  DHSet<TopSymbolIndex<TermList>::Entry> _variables;
};

struct NoTerms {};

// selected non-equation literals
class DelayedNonEquations: public TopSymbolIndex<NoTerms> {
public:
  CLASS_NAME(DelayedNonEquations);
  USE_ALLOCATOR(DelayedNonEquations);
};

/**
 * base class for delayed inferences (so far superposition, resolution)
 * provides mightPossiblyUnify() but is otherwise a GeneratingInferenceEngine
 */
class DelayedInference: public GeneratingInferenceEngine {
public:
  CLASS_NAME(DelayedInference);
  USE_ALLOCATOR(DelayedInference);
  DelayedInference(Ordering *ord, Options const *opts)
    : _ord(ord)
    , _opts(opts)
  {}

  /**
   * check whether left and right may eventually unify modulo some theory
   * should generally err on the side of caution and return true
   */
  bool mightPossiblyUnify(TermList left, TermList right) {
    // TODO do something sensible here
    return true;
  }

protected:
  Ordering     * const _ord;
  Options const* const _opts;
};

// a delayed-unification version of superposition
class DelayedSuperposition: public DelayedInference {
public:
  CLASS_NAME(DelayedSuperposition);
  USE_ALLOCATOR(DelayedSuperposition);

  DelayedSuperposition(Ordering* ord, Options const* opts)
    : DelayedInference(ord, opts)
    , _subtermIndex()
    , _lhsIndex()
    {}

  void attach(SaturationAlgorithm* salg) final override;
  ClauseIterator generateClauses(Clause* premise) final override;
#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& is) final override
  {
    _subtermIndex = static_cast<decltype(_subtermIndex)>(is[0]);
    _lhsIndex     = static_cast<decltype(    _lhsIndex)>(is[1]);
  }
#endif 

private:
  Clause *perform(Clause *, Literal *, TermList, Clause *, Literal *, Term *);

  DelayedSubterms *_subtermIndex;
  DelayedLHS *_lhsIndex;
};

class DelayedEqualityFactoring: public GeneratingInferenceEngine {
public:
  CLASS_NAME(DelayedEqualityFactoring);
  USE_ALLOCATOR(DelayedEqualityFactoring);
  DelayedEqualityFactoring(Ordering* ord, Options const* opts) 
    : _ord(ord)
    , _opts(opts) 
    {}

  void attach(SaturationAlgorithm* salg) final override;
  ClauseIterator generateClauses(Clause* premise) final override;

private:

  Clause* perform(Clause* cl,
    unsigned lit1,
    unsigned term1,
    unsigned lit2,
    unsigned term2) const;

  Ordering     * const _ord;
  Options const* const _opts;
};


class DelayedEqualityResolution: public GeneratingInferenceEngine {
public:
  CLASS_NAME(DelayedEqualityResolution);
  USE_ALLOCATOR(DelayedEqualityResolution);
  DelayedEqualityResolution(Ordering* ord, Options const* opts) 
    : _ord(ord)
    , _opts(opts) 
    {}

  void attach(SaturationAlgorithm* salg) final override;
  ClauseIterator generateClauses(Clause* premise) final override;

private:
  Clause *perform(Clause *, unsigned idx) const;

  Ordering     * const _ord;
  Options const* const _opts;
};

} // namespace Inferences

#endif
