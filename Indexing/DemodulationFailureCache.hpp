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
 * @file DemodulationFailureCache.hpp
 * A cache of failed generalization queries of forward demodulation that does not
 * change any result (see DemodulationFailureCache).
 */

#ifndef __Indexing_DemodulationFailureCache__
#define __Indexing_DemodulationFailureCache__

#include <cstdint>
#include <vector>
#if defined(__linux__)
#include <sys/mman.h>
#endif

#include "Forwards.hpp"
#include "Kernel/Term.hpp"

using namespace Kernel;

namespace Indexing {

/** Allocator for the cache's tables: serves memory aligned to huge-page boundaries and
 * advised to the huge-page pager, so the tables' random probes cost a few TLB entries
 * instead of page walks. The block is cut out of the raw allocation with enough slack
 * below it to be huge-page aligned and to keep the raw pointer; the slack is never
 * touched, so it costs address space only. */
template<class T>
struct HugePageAllocator
{
  using value_type = T;
  static constexpr std::size_t HUGE_PAGE = std::size_t(1) << 21;

  T* allocate(std::size_t n)
  {
    if (!n) {
      return nullptr;
    }
    std::size_t bytes = n * sizeof(T);
    // enough slack to align the block up to a huge-page boundary while keeping at least
    // the pointer's eight bytes below it inside the allocation
    std::size_t slack = HUGE_PAGE + 64;
    char* raw = static_cast<char*>(::operator new(bytes + slack));
    char* block = reinterpret_cast<char*>(
        (reinterpret_cast<uintptr_t>(raw) + slack - 1) & ~(HUGE_PAGE - 1));
    *reinterpret_cast<char**>(block - 8) = raw;
#if defined(MADV_HUGEPAGE)
    // a fault in an advised, huge-page-aligned region takes a huge page directly;
    // regions smaller than a huge page, and the pager without huge pages, ignore it
    madvise(block, bytes, MADV_HUGEPAGE);
#endif
    return reinterpret_cast<T*>(block);
  }

  void deallocate(T* p, std::size_t) noexcept
  {
    if (p) {
      ::operator delete(*reinterpret_cast<char**>(reinterpret_cast<char*>(p) - 8));
    }
  }
};

template<class T, class U>
bool operator==(const HugePageAllocator<T>&, const HugePageAllocator<U>&) { return true; }
template<class T, class U>
bool operator!=(const HugePageAllocator<T>&, const HugePageAllocator<U>&) { return false; }


/**
 * Cache of failed generalization queries of forward demodulation (option demodulation_cache).
 *
 * Two kinds of failures are recorded: terms of which the lookup found no generalization at
 * all, and -- with APPLICABILITY -- terms of which every generalization found was rejected
 * by a check that does not depend on the clause being simplified, the ordering check
 * (rejections by the color or the redundancy check do depend on it, and block the
 * recording). Whether some generalization rewrites a term can depend on the clause, but
 * that none can does not.
 * A failure stays valid until a demodulator is added whose left-hand side has the same
 * top symbol as the term. Top symbols are grouped into BUCKETS groups with a counter each,
 * which is increased whenever a left-hand side with a top symbol of the group is added.
 *
 * A term is also recorded as clean together with all its subterms, with the set of groups of
 * the top symbols of all of them and the sum of their counters: as counters only increase,
 * an unchanged sum means that no relevant demodulator was added. Clean terms are built
 * bottom-up: a term becomes clean when its own failure is valid and all its arguments are clean.
 *
 * Entries live in a dense array indexed by term ID, capped at MAX_DENSE_ENTRIES. Beyond the
 * cap (or for every term when IDs are randomized) they live in a table of at most
 * 2^OVERFLOW_BITS slots keyed by term identity that evicts on collision. A lost entry is a
 * missed skip, never a wrong one: the stored key proves which term an entry describes. The
 * table grows only when an evicted term claims its slot again (re-reference): only revisits,
 * not one-time traffic, pay for growth.
 */
struct DemodulationFailureCache
{
  static DemodulationFailureCache& get();

  bool enabled = false;

  /** one bit of the dependency mask per bucket, so an entry's mask fits next to its
   *  16-bit epoch fields in 8 bytes (see Entry) */
  static constexpr unsigned BUCKET_BITS = 5;
  static constexpr unsigned BUCKETS = 1u << BUCKET_BITS;
  /** "no value" for the 16-bit entry fields */
  static constexpr uint16_t NONE16 = ~uint16_t(0);
  /** total number of bucket bumps (the sum of all epochs) after which all entries are
   *  wiped and the epochs restart, so the stored epochs and dependency-mask sums stay
   *  exact within their 16-bit entry fields and NONE16 stays unreachable as a live
   *  value. The heaviest observed run bumps ~140k times in 30 s: such a run wipes about
   *  twice, losing entries until the traffic that recorded them fails again. */
  static constexpr uint64_t EPOCH_LIMIT = NONE16 - 1;

  /** the applicability extension: lookups whose every generalization is rejected by a check
   *  that does not depend on the clause being simplified (the ordering checks) count as
   *  failures too */
  static constexpr bool APPLICABILITY = true;

  /** ceiling of the overflow table (slots = 2^bits), keeping it cache-resident: a probe
   *  of a table that no longer fits in the last-level cache costs about as much as the
   *  term-index lookup a hit saves, so a bigger table can only lose. Growth stops on its
   *  own when evictions stop coming back. */
  static constexpr unsigned OVERFLOW_BITS = 18;

  static unsigned bucket(unsigned functor) { return (functor * 0x9e3779b1u) >> (32 - BUCKET_BITS); }

  /** Start a new index. Randomized IDs require identity-based sparse storage. */
  void reset(bool enable, bool sparseIds = false, unsigned overflowBits = OVERFLOW_BITS);
  void onInsertLhs(TermList lhs);

  /** whether the lookup for @b t is known to find nothing */
  bool failureKnown(Term* t);
  /** whether the lookups for @b t and all its subterms are known to find nothing */
  bool subtreeClean(Term* t);
  void recordFailure(Term* t);
  /** prefetch the entries of @b t's arguments: subtreeClean validates them right after
   *  the failure of @b t becomes known, and after a lookup for @b t itself the terms
   *  visited next are @b t's arguments, so the lookup's latency can hide their misses */
  void prefetchArguments(Term* t);

  /** re-references seen by the bounded overflow table: evicted terms claiming their
   *  slot again. The only growth signal above the bootstrap region; the surplus is
   *  decayed by the amount kept after growing (see overflowEntry). */
  uint64_t overflowHot = 0;
  /** live entries in the overflow table */
  uint64_t overflowLive = 0;

private:
  struct Entry {
    uint32_t subtreeMask = 0;
    uint16_t failureEpoch = NONE16;
    uint16_t subtreeSum = NONE16;
  };
  static_assert(sizeof(Entry) == 8, "the dense table is sized by this");
  /** one slot of the bounded table that backs the cache beyond the dense array */
  struct OverflowSlot {
    Term* term = nullptr;
    Entry entry;
  };
  static_assert(sizeof(OverflowSlot) == 16, "the overflow table is sized by this");
  static constexpr unsigned OVERFLOW_MIN_BITS = 12;
  /** ceiling for the table: 2^18 slots (6 MB with the victim shadow) still fit in the
   *  last-level cache; a larger hot set was observed to grow the table to 2^21 slots and
   *  pay for it in misses and evictions. Growth stops on its own much earlier when
   *  evictions stop coming back */
  static constexpr unsigned OVERFLOW_MAX_BITS = 18;
  /** grow once hot evictions (an evicted term claiming its slot again) exceed one eighth of
   *  the slot count; the table grows for revisits, never for one-time traffic */
  static constexpr unsigned OVERFLOW_HOT_DIVISOR = 8;
  /** occupancy alone grows the table only below this many slots: a small table cannot see a
   *  much larger hot set coming back (the victim shadow forgets long-evicted terms), so the
   *  cheap region bootstraps on occupancy and re-reference takes over beyond it */
  static constexpr unsigned OVERFLOW_BOOTSTRAP_BITS = 16;

  /** the cache's tables, on huge pages (see HugePageAllocator) */
  using DenseTable = std::vector<Entry, HugePageAllocator<Entry>>;
  using OverflowTable = std::vector<OverflowSlot, HugePageAllocator<OverflowSlot>>;
  using GhostTable = std::vector<Term*, HugePageAllocator<Term*>>;

  /** read access: the entry of @b t, or nullptr when none was recorded */
  Entry* findEntry(Term* t);
  /** prefetch the cache line of @b t's entry, the way findEntry reads it */
  void prefetchEntry(Term* t);
  /** write access: the entry of @b t, claiming it (evicting on collision) if needed */
  Entry& entry(Term* t);
  uint16_t sum(uint32_t mask);
  bool subtreeValid(const Entry& e);
  void discardEntries();
  size_t overflowIndex(Term* t) const;
  Entry* overflowFind(Term* t);
  Entry& overflowEntry(Term* t);
  void overflowGrow();

  /** epoch counters, one per bucket; a single cache line at 32 buckets */
  uint16_t _epochs[BUCKETS] = {};
  /** the sum of all epochs; each insertion adds one per bucket it bumps */
  uint64_t _epochSum = 0;
  // Random traversals perturb the high bits of term IDs. Keep those IDs sparse,
  // and bound the dense allocation even on runs with many ordinary shared terms.
  static constexpr unsigned MAX_DENSE_ENTRIES = 1u << 20;
  unsigned _denseIdLimit = MAX_DENSE_ENTRIES;
  DenseTable _entries;
  unsigned _overflowBits = OVERFLOW_BITS;
  OverflowTable _overflow;
  /** victim shadow: _ghost[i] is the term last evicted from _overflow[i]. When that term
   *  claims its slot again it was re-referenced after eviction (a hot eviction) -- evidence
   *  that a bigger table would buy hits. Never answers a query, so it cannot change results. */
  GhostTable _ghost;
  /** 64 - log2 of _overflow.size(), or 64 while the table is empty */
  unsigned _overflowShift = 64;
};

} // namespace Indexing

#endif // __Indexing_DemodulationFailureCache__
