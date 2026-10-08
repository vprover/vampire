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
 * @file DemodulationFailureCache.cpp
 * The cache of failed generalization queries of forward demodulation (see the header).
 */

#include <algorithm>
#include <iomanip>

#include "Shell/UIHelper.hpp"

#include "DemodulationFailureCache.hpp"

using Shell::addCommentSignForSZS;

namespace Indexing {

DemodulationFailureCache& DemodulationFailureCache::get()
{
  static DemodulationFailureCache cache;
  return cache;
}

void DemodulationFailureCache::reset(bool enable, bool sparseIds, unsigned overflowBits)
{
  enabled = enable;
  _denseIdLimit = sparseIds ? 0 : MAX_DENSE_ENTRIES;
  _overflowBits = std::min(std::max(overflowBits, 1u), OVERFLOW_MAX_BITS);
  std::fill(std::begin(_epochs), std::end(_epochs), 0u);
  _epochSum = 0;
  _entries.clear();
  std::vector<OverflowSlot>().swap(_overflow);
  std::vector<Term*>().swap(_ghost);
  _overflowShift = 64;
  queries = lookupsSkipped = subtreesSkipped = failuresRecorded = 0;
  overflowFills = overflowEvictions = overflowGrowths = overflowRehashDrops = overflowLive = 0;
  overflowHot = 0;
  bucketBumps = wipes = 0;
}

void DemodulationFailureCache::discardEntries()
{
  std::vector<Entry>().swap(_entries);
  std::vector<OverflowSlot>().swap(_overflow);
  std::vector<Term*>().swap(_ghost);
  _overflowShift = 64;
  overflowLive = 0;
  wipes++;
}

void DemodulationFailureCache::onInsertLhs(TermList lhs)
{
  if (lhs.isVar()) {
    // a variable could generalize anything
    for (unsigned b = 0; b < BUCKETS; b++) {
      _epochs[b]++;
    }
    _epochSum += BUCKETS;
    bucketBumps += BUCKETS;
  } else {
    _epochs[bucket(lhs.term()->functor())]++;
    _epochSum++;
    bucketBumps++;
  }
  if (_epochSum >= EPOCH_LIMIT) {
    // reached by the heaviest runs (~140k bucket bumps in 30 s): wipe all entries
    // and restart the epochs, so the 16-bit stored epochs and mask sums stay exact
    discardEntries();
    std::fill(std::begin(_epochs), std::end(_epochs), 0u);
    _epochSum = 0;
  }
}

DemodulationFailureCache::Entry& DemodulationFailureCache::entry(Term* t)
{
  unsigned id = t->getId();
  if (id >= _entries.size()) {
    if (id >= _denseIdLimit) {
      return overflowEntry(t);
    }
    unsigned target = std::min(_denseIdLimit, id + id / 2 + 1024);
    // reserve allocates exactly the target: the 1.5x growth of the target keeps
    // reallocation amortized, and no allocation overshoots the dense limit the
    // way the vector's own geometric growth would
    _entries.reserve(target);
    _entries.resize(target);
  }
  return _entries[id];
}

DemodulationFailureCache::Entry* DemodulationFailureCache::findEntry(Term* t)
{
  unsigned id = t->getId();
  if (id < _entries.size()) {
    return &_entries[id];
  }
  return overflowFind(t);
}

size_t DemodulationFailureCache::overflowIndex(Term* t) const
{
  // the top bits of the Fibonacci-hashed pointer: every bit of the identity, spread
  ASS(_overflowShift < 64);
  return (reinterpret_cast<uintptr_t>(t) * 0x9e3779b97f4a7c15ull) >> _overflowShift;
}

DemodulationFailureCache::Entry* DemodulationFailureCache::overflowFind(Term* t)
{
  if (_overflow.empty()) {
    return nullptr;
  }
  OverflowSlot& slot = _overflow[overflowIndex(t)];
  return slot.term == t ? &slot.entry : nullptr;
}

DemodulationFailureCache::Entry& DemodulationFailureCache::overflowEntry(Term* t)
{
  if (_overflow.empty()) {
    unsigned bits = std::min(_overflowBits, OVERFLOW_MIN_BITS);
    _overflow.resize(size_t(1) << bits);
    _ghost.assign(_overflow.size(), nullptr);
    _overflowShift = 64 - bits;
  } else if (64 - _overflowShift < _overflowBits) {
    // Growth is paid for by re-reference: an evicted term claiming its slot again
    // (a hot eviction, seen through the victim shadow) is the only signal that a
    // bigger table would buy hits -- one-time traffic evicts entries that never
    // come back and gains nothing from capacity. Occupancy alone bootstraps only
    // the cheap region below 2^OVERFLOW_BOOTSTRAP_BITS slots, where the shadow
    // cannot see a much larger hot set coming back.
    size_t size = _overflow.size();
    bool hotGrowth = overflowHot * OVERFLOW_HOT_DIVISOR > size;
    bool bootstrap = size < (size_t(1) << OVERFLOW_BOOTSTRAP_BITS)
                     && overflowLive * 8 > size * 7;
    if (hotGrowth || bootstrap) {
      overflowGrow();
      if (hotGrowth) {
        // keep the surplus: sustained re-reference keeps growing without having
        // to re-earn the whole (now doubled) threshold from scratch
        overflowHot -= std::min<uint64_t>(overflowHot, size / OVERFLOW_HOT_DIVISOR);
      }
    }
  }
  size_t idx = overflowIndex(t);
  OverflowSlot& slot = _overflow[idx];
  if (slot.term != t) {
    bool hot = _ghost[idx] == t; // t was this slot's last victim: it is back
    if (slot.term) {
      ++overflowEvictions;
      _ghost[idx] = slot.term; // remember the new victim
    } else {
      ++overflowFills;
      ++overflowLive;
    }
    if (hot) {
      ++overflowHot;
    }
    slot.term = t;
    slot.entry = Entry();
  }
  return slot.entry;
}

void DemodulationFailureCache::overflowGrow()
{
  ASS(_overflowShift > 64 - _overflowBits); // not at the configured ceiling yet
  std::vector<OverflowSlot> previous;
  previous.swap(_overflow);
  std::vector<Term*> previousGhost;
  previousGhost.swap(_ghost);
  unsigned bits = 65 - _overflowShift;
  _overflow.resize(size_t(1) << bits);
  _ghost.assign(_overflow.size(), nullptr);
  _overflowShift = 64 - bits;
  ++overflowGrowths;
  for (OverflowSlot& slot : previous) {
    if (!slot.term) {
      continue;
    }
    OverflowSlot& target = _overflow[overflowIndex(slot.term)];
    if (target.term) {
      ++overflowRehashDrops; // unreachable: doubling splits every slot into a disjoint pair
      --overflowLive;
      continue;
    }
    target = slot;
  }
  for (Term* victim : previousGhost) {
    if (!victim) {
      continue;
    }
    Term*& target = _ghost[overflowIndex(victim)];
    if (!target) {
      // likewise unreachable: each victim rehashes with the slot it was evicted from
      target = victim;
    }
  }
}

uint16_t DemodulationFailureCache::sum(uint32_t mask)
{
  uint32_t res = 0;
  while (mask) {
    res += _epochs[__builtin_ctz(mask)];
    mask &= mask - 1;
  }
  // a sum over a subset of the epochs is at most their total, kept below EPOCH_LIMIT
  ASS_L(res, NONE16);
  return uint16_t(res);
}

bool DemodulationFailureCache::subtreeValid(const Entry& e)
{
  if (e.subtreeSum == NONE16) {
    return false;
  }
  return sum(e.subtreeMask) == e.subtreeSum;
}

bool DemodulationFailureCache::failureKnown(Term* t)
{
  Entry* e = findEntry(t);
  return e && e->failureEpoch == _epochs[bucket(t->functor())];
}

void DemodulationFailureCache::recordFailure(Term* t)
{
  Entry& e = entry(t);
  e.failureEpoch = _epochs[bucket(t->functor())];
  failuresRecorded++;
}

bool DemodulationFailureCache::subtreeClean(Term* t)
{
  if (Entry* e = findEntry(t)) {
    if (subtreeValid(*e)) {
      return true;
    }
  }
  if (!failureKnown(t)) {
    return false;
  }
  // t itself finds nothing; it is clean if all its arguments are (type arguments are not visited)
  uint32_t mask = uint32_t(1) << bucket(t->functor());
  for (unsigned i = t->numTypeArguments(); i < t->arity(); i++) {
    TermList arg = *t->nthArgument(i);
    if (arg.isVar()) {
      continue;
    }
    Term* a = arg.term();
    if (!a->shared() || a->isSpecial()) {
      return false;
    }
    Entry* ea = findEntry(a);
    if (!ea || !subtreeValid(*ea)) {
      return false;
    }
    mask |= ea->subtreeMask;
  }
  // entry() may claim a sparse slot or grow the table, so it is looked up again
  Entry& e = entry(t);
  e.subtreeMask = mask;
  e.subtreeSum = sum(mask);
  return true;
}

static std::ostream& line(std::ostream& out, const char* label)
{
  addCommentSignForSZS(out);
  return out << "  " << std::left << std::setw(44) << label << std::right;
}

static double pct(double part, double whole) { return whole ? 100.0 * part / whole : 0.0; }

void DemodulationFailureCache::print(std::ostream& out) const
{
  addCommentSignForSZS(out);
  out << "Forward demodulation failure cache\n";
  out << std::fixed << std::setprecision(2);
  line(out, "cacheable subterm visits") << queries << "\n";
  line(out, "lookups skipped (failure known)") << pct(lookupsSkipped, queries) << "%\n";
  line(out, "subterms skipped with all their subterms") << pct(subtreesSkipped, queries) << "%\n";
  line(out, "failures recorded / table size") << failuresRecorded << " / " << _entries.size() + overflowLive << "\n";
  line(out, "overflow slots / live") << _overflow.size() << " / " << overflowLive << "\n";
  line(out, "overflow fills / evictions / hot / growths") << overflowFills << " / " << overflowEvictions
      << " / " << overflowHot << " / " << overflowGrowths << "\n";
  line(out, "bucket bumps / epoch wipes") << bucketBumps << " / " << wipes << "\n";
  out << std::defaultfloat << std::setprecision(6);
}

} // namespace Indexing
