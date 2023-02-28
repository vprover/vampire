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

#include "Kernel/Clause.hpp"
#include "Indexing/Index.hpp"
#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

// base class for delayed unification "indices"
class TopSymbolIndex {
public:
  template<typename T>
  struct Entry {
    Clause *clause;
    Literal *literal;
    T term;

    Entry<TermList> termList() { return { clause, literal, TermList(term) }; }

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
    decltype(_functors)::Iterator it(_functors);
    while(it.hasNext())
      delete it.next();
  }

  void handle(Clause *c, Literal *l, Term *t, bool adding) {
    CALL("TopSymbolIndex::handle")
    typedef DHSet<Entry<Term *>> Entries;

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

  VirtualIterator<Entry<Term *>> entries() {
    return pvi(getMapAndFlattenIterator(
      _functors.range(),
      [](DHSet<Entry<Term *>> *entries) { return entries->iterator(); }
    ));
  }

  VirtualIterator<Entry<Term *>> query(unsigned functor) {
    CALL("TopSymbolIndex::query")
    DHSet<Entry<Term *>> *entries;
    if(!_functors.find(functor, entries))
      return VirtualIterator<Entry<Term *>>::getEmpty();
    return entries->iterator();
  }

private:
  // map from functors to a set of clause/literal pairs
  // TODO DHSet doesn't have a move constructor so it has to be heap-allocated
  // Johannes has already fixed this in the substitution-tree refactor, drop the indirection when we can
  DHMap<unsigned, DHSet<Entry<Term *>> *> _functors;
};

// non-variable subterms of selected literals
class DelayedSubterms: public Indexing::Index, public TopSymbolIndex {
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
class DelayedLHS: public Indexing::Index, public TopSymbolIndex {
public:
  CLASS_NAME(DelayedLHS);
  USE_ALLOCATOR(DelayedLHS);

  DelayedLHS(const Ordering &ordering, const Options &options) : _ordering(ordering), _options(options) {}
  void handleClause(Kernel::Clause* c, bool adding) override;
  // variable left-hand-sides
  DHSet<Entry<TermList>>::Iterator variables() {
    return decltype(_variables)::Iterator(_variables);
  }

private:
  // current ordering
  const Ordering& _ordering;
  // current options
  const Options &_options;

  DHSet<Entry<TermList>> _variables;
};


// a delayed-unification version of superposition
class DelayedSuperposition: public GeneratingInferenceEngine {
public:
  CLASS_NAME(DelayedSuperposition);
  USE_ALLOCATOR(DelayedSuperposition);
  DelayedSuperposition(Ordering* ord, Options const* opts) 
    : _subtermIndex()
    , _lhsIndex()
    , _ord(ord)
    , _opts(opts) 
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
  Ordering     * const _ord;
  Options const* const _opts;
};

} // namespace Inferences

#endif
