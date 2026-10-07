/*
 * This file is part of Vampire, distributed under the licence in the source directory.
 */
#include <string>
#include <vector>

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/DemodulationFailureCache.hpp"

using namespace Test;
using Indexing::DemodulationFailureCache;

static Kernel::Term* term(TermSugar t) { return Kernel::TermList(t).term(); }

TEST_FUN(failures_and_insertions) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  auto fa = term(f(a));
  DemodulationFailureCache cache;
  ASS(!cache.failureKnown(fa));
  cache.recordFailure(fa);
  ASS(cache.failureKnown(fa));
  ASS_NEQ(cache.bucket(fa->functor()), cache.bucket(term(g(a))->functor()));
  cache.onInsertLhs(g(x));
  ASS(cache.failureKnown(fa));
  cache.onInsertLhs(f(x));
  ASS(!cache.failureKnown(fa));
  cache.recordFailure(fa);
  cache.onInsertLhs(x);
  ASS(!cache.failureKnown(fa));
}

TEST_FUN(subtree_invalidation) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  auto aa = term(a), ga = term(g(a)), fga = term(f(g(a)));
  DemodulationFailureCache cache;
  cache.recordFailure(fga);
  ASS(!cache.subtreeClean(fga));
  cache.recordFailure(aa);
  ASS(cache.subtreeClean(aa));
  cache.recordFailure(ga);
  ASS(cache.subtreeClean(ga));
  ASS(cache.subtreeClean(fga));
  cache.onInsertLhs(g(x));
  ASS(cache.failureKnown(fga));
  ASS(!cache.subtreeClean(fga));
  cache.recordFailure(ga);
  ASS(cache.subtreeClean(ga));
  ASS(cache.subtreeClean(fga));
  cache.onInsertLhs(x);
  ASS(!cache.subtreeClean(fga));
}

TEST_FUN(bucket_collisions_are_conservative) {
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DemodulationFailureCache cache;
  auto aa = term(a);
  cache.recordFailure(aa);
  ASS(cache.subtreeClean(aa));
  // More than BUCKETS different symbols force a collision with a eventually.
  Kernel::Term* collision = nullptr;
  for (unsigned i = 0; i < 1024 && !collision; i++) {
    auto b = FuncSugar("collision_" + std::to_string(i), {}, srt)();
    if (cache.bucket(term(b)->functor()) == cache.bucket(aa->functor())) {
      collision = term(b);
    }
  }
  ASS(collision);
  ASS_NEQ(collision->functor(), aa->functor());
  cache.onInsertLhs(Kernel::TermList(collision));
  ASS(!cache.failureKnown(aa));
  ASS(!cache.subtreeClean(aa));
}

TEST_FUN(variables_and_reset) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC(f, {srt}, srt)
  auto fx = term(f(x));
  DemodulationFailureCache cache;
  cache.reset(true);
  cache.recordFailure(fx);
  ASS(cache.subtreeClean(fx));
  cache.reset(false);
  ASS(!cache.enabled);
  ASS_EQ(cache.failuresRecorded, 0);
  ASS(!cache.failureKnown(fx));
  ASS(!cache.subtreeClean(fx));
}

TEST_FUN(sparse_ids_and_subtree_storage_growth) {
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_FUNC(f, {srt}, srt)
  auto aa = term(a), bb = term(b), fa = term(f(a));
  auto originalId = aa->getId();
  auto originalBId = bb->getId();
  // Model the large IDs assigned by --random_traversals; this must not allocate
  // an array with billions of entries. Unit tests run in isolated processes.
  aa->setId(0xf0000000u);
  bb->setId(0xf0000000u);
  DemodulationFailureCache cache;
  cache.recordFailure(fa);
  ASS(!cache.subtreeClean(fa));
  cache.recordFailure(aa);
  ASS(!cache.failureKnown(bb));
  ASS(cache.subtreeClean(aa));
  ASS(cache.subtreeClean(fa));
  cache.onInsertLhs(a);
  ASS(!cache.subtreeClean(fa));
  aa->setId(originalId);
  bb->setId(originalBId);
}

TEST_FUN(dense_storage_growth) {
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  auto aa = term(a), fa = term(f(a));
  auto originalId = aa->getId();
  aa->setId(100000);
  DemodulationFailureCache cache;
  cache.recordFailure(fa);
  // Looking up the child grows storage while examining the parent's summary.
  ASS(!cache.subtreeClean(fa));
  cache.recordFailure(aa);
  ASS(cache.subtreeClean(aa));
  ASS(cache.subtreeClean(fa));
  aa->setId(originalId);
}

TEST_FUN(randomized_id_collisions_use_term_identity) {
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  auto aa = term(a), bb = term(b);
  auto originalAId = aa->getId(), originalBId = bb->getId();
  // Randomized IDs can wrap to small values as the shared-term table grows.
  // Sparse mode must distinguish terms even when their IDs are equal and small.
  aa->setId(0);
  bb->setId(0);
  DemodulationFailureCache cache;
  cache.reset(true, true);
  cache.recordFailure(aa);
  ASS(cache.failureKnown(aa));
  ASS(!cache.failureKnown(bb));
  cache.recordFailure(bb);
  ASS(cache.subtreeClean(aa));
  ASS(cache.subtreeClean(bb));
  ASS_NEQ(cache.bucket(aa->functor()), cache.bucket(bb->functor()));
  cache.onInsertLhs(a);
  ASS(cache.subtreeClean(bb)); // only a's bucket was bumped; b's summary is unchanged
  ASS(!cache.subtreeClean(aa)); // equal IDs must not make a's summary valid again
  aa->setId(originalAId);
  bb->setId(originalBId);
}

TEST_FUN(overflow_table_eviction_is_exact) {
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  auto aa = term(a);
  auto originalId = aa->getId();
  aa->setId(0xf0000000u);
  DemodulationFailureCache cache;
  // same-bucket terms: if the table confused their entries, a fresh entry of
  // another term would validate aa's lookup and skip it wrongly
  std::vector<Kernel::Term*> others;
  std::vector<unsigned> originalIds;
  for (unsigned i = 0; others.size() < 40 && i < 100000; i++) {
    auto b = term(FuncSugar("overflow_evict_" + std::to_string(i), {}, srt)());
    if (cache.bucket(b->functor()) != cache.bucket(aa->functor())) {
      continue;
    }
    originalIds.push_back(b->getId());
    b->setId(0xf1000000u + unsigned(others.size()));
    others.push_back(b);
  }
  ASS_EQ(others.size(), 40);
  cache.reset(true, false, 4); // 16 slots
  cache.recordFailure(aa);
  ASS(cache.failureKnown(aa));
  cache.onInsertLhs(a); // bumps the bucket all of them live in
  ASS(!cache.failureKnown(aa));
  for (Kernel::Term* t : others) {
    cache.recordFailure(t);
  }
  // 41 distinct terms passed through 16 slots: entries were evicted, but no
  // lookup may be answered from another term's entry
  ASS_G(cache.overflowEvictions, 0);
  ASS_LE(cache.overflowLive, 16);
  unsigned known = 0;
  for (Kernel::Term* t : others) {
    known += cache.failureKnown(t);
  }
  ASS_G(known, 0);
  ASS_LE(known, 16);
  ASS(!cache.failureKnown(aa)); // evicted or stale, never another term's entry
  cache.recordFailure(aa);
  ASS(cache.failureKnown(aa));
  aa->setId(originalId);
  for (unsigned i = 0; i < others.size(); i++) {
    others[i]->setId(originalIds[i]);
  }
}

TEST_FUN(overflow_subtree_summaries) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  DECL_FUNC(g, {srt}, srt)
  auto aa = term(a), ga = term(g(a)), fga = term(f(g(a)));
  auto originalAId = aa->getId(), originalGId = ga->getId(), originalFId = fga->getId();
  // beyond the dense limit: entries live in the bounded table
  aa->setId(0xf0000000u);
  ga->setId(0xf0000001u);
  fga->setId(0xf0000002u);
  DemodulationFailureCache cache;
  cache.reset(true, false, 12);
  ASS_NEQ(cache.bucket(fga->functor()), cache.bucket(ga->functor()));
  cache.recordFailure(fga);
  ASS(!cache.subtreeClean(fga));
  cache.recordFailure(ga);
  ASS(!cache.subtreeClean(fga));
  cache.recordFailure(aa);
  ASS(cache.subtreeClean(aa));
  ASS(cache.subtreeClean(ga));
  ASS(cache.subtreeClean(fga));
  ASS_EQ(cache.overflowLive, 3);
  ASS_EQ(cache.overflowEvictions, 0);
  cache.onInsertLhs(g(x));
  ASS(cache.failureKnown(fga));
  ASS(!cache.subtreeClean(fga));
  cache.recordFailure(ga);
  ASS(cache.subtreeClean(ga));
  ASS(cache.subtreeClean(fga));
  cache.onInsertLhs(x);
  ASS(!cache.subtreeClean(fga));
  aa->setId(originalAId);
  ga->setId(originalGId);
  fga->setId(originalFId);
}

TEST_FUN(overflow_growth_and_rehash) {
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  // 10000 distinct shared terms: enough single visits to fill 7/8 of the
  // initial table, and every one of them has the same top symbol
  Kernel::TermList current = a;
  std::vector<Kernel::Term*> terms;
  std::vector<unsigned> originalIds;
  for (unsigned i = 0; i < 10000; i++) {
    current = f(current);
    Kernel::Term* t = current.term();
    originalIds.push_back(t->getId());
    t->setId(0xf0000000u + i);
    terms.push_back(t);
  }
  DemodulationFailureCache cache;
  cache.reset(true, false, 14);
  for (Kernel::Term* t : terms) {
    cache.recordFailure(t);
  }
  // occupancy bootstrapped the table from 4096 to 8192 slots once -- no term was
  // recorded twice, so no hot eviction could add to it; doubling is lossless
  // (every slot splits into a disjoint pair) and every entry must answer exactly
  ASS_EQ(cache.overflowGrowths, 1);
  ASS_EQ(cache.overflowRehashDrops, 0);
  unsigned known = 0;
  for (Kernel::Term* t : terms) {
    known += cache.failureKnown(t);
  }
  ASS_GE(known, 3000);
  ASS_EQ(known, cache.overflowLive);
  cache.recordFailure(terms.front());
  ASS(cache.failureKnown(terms.front()));
  for (unsigned i = 0; i < terms.size(); i++) {
    terms[i]->setId(originalIds[i]);
  }
}

TEST_FUN(overflow_grows_on_hot_evictions) {
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  // 4000 distinct terms into a 4096-slot table: one pass of single visits must
  // not grow it, but recording every term again -- the evicted ones claiming
  // their slots back -- is re-reference and must
  Kernel::TermList current = a;
  std::vector<Kernel::Term*> terms;
  std::vector<unsigned> originalIds;
  for (unsigned i = 0; i < 4000; i++) {
    current = f(current);
    Kernel::Term* t = current.term();
    originalIds.push_back(t->getId());
    t->setId(0xf0000000u + i);
    terms.push_back(t);
  }
  DemodulationFailureCache cache;
  cache.reset(true, false, 20);
  for (Kernel::Term* t : terms) {
    cache.recordFailure(t);
  }
  // one-time traffic fills well below the bootstrap threshold and no term was
  // evicted and recorded again: no growth, no hot evictions
  ASS_EQ(cache.overflowGrowths, 0);
  ASS_EQ(cache.overflowHot, 0);
  for (Kernel::Term* t : terms) {
    cache.recordFailure(t);
  }
  // the evicted terms came back and claimed their slots: re-reference was seen
  // and paid for growth
  ASS_G(cache.overflowHot, 0);
  ASS_G(cache.overflowGrowths, 1);
  // and every live entry still answers exactly
  unsigned known = 0;
  for (Kernel::Term* t : terms) {
    known += cache.failureKnown(t);
  }
  ASS_EQ(known, cache.overflowLive);
  for (unsigned i = 0; i < terms.size(); i++) {
    terms[i]->setId(originalIds[i]);
  }
}

TEST_FUN(overflow_reads_do_not_allocate) {
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_FUNC(f, {srt}, srt)
  auto aa = term(a), fa = term(f(a));
  auto originalAId = aa->getId(), originalFId = fa->getId();
  aa->setId(0xf0000000u);
  fa->setId(0xf0000001u);
  DemodulationFailureCache cache;
  cache.reset(true, false, 12);
  // queries for terms with no entry must not claim slots
  ASS(!cache.failureKnown(fa));
  ASS(!cache.subtreeClean(fa));
  ASS_EQ(cache.overflowLive, 0);
  cache.recordFailure(aa);
  ASS_EQ(cache.overflowLive, 1);
  ASS(cache.failureKnown(aa));
  ASS(!cache.subtreeClean(fa));
  ASS_EQ(cache.overflowLive, 1);
  aa->setId(originalAId);
  fa->setId(originalFId);
}
