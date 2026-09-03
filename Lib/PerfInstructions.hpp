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
 * @file PerfInstructions.hpp
 * Reading the hardware "instructions retired" counter cheaply, from user space.
 *
 * Lib/Timer.cpp opens a PERF_COUNT_HW_INSTRUCTIONS event and reads it with
 * read(PERF_FD), which costs a syscall (measured: ~560ns). That is fine for the
 * timer thread's periodic limit check, but far too slow for a counter we want to
 * sample on every TIME_TRACE scope.
 *
 * The fast path is to mmap the same file descriptor -- which yields a
 * struct perf_event_mmap_page -- and read the counter register directly with the
 * rdpmc instruction. Measured on the reference server: 8.9ns, against 27.5ns for
 * clock_gettime(CLOCK_MONOTONIC), i.e. cheaper than the clock read the profiler
 * already does.
 *
 * IMPORTANT: instructionCount() may only be called from the thread that
 * Timer::reinitialise() ran on -- in practice, Vampire's main thread. rdpmc reads
 * the performance counter register of whatever CPU the *caller* is running on,
 * which for any other thread is not this event at all. The `index` check below
 * catches the common case (returning -1 so the caller can fall back), but it is not
 * a guarantee, so do not call this from timer_thread; use
 * Timer::updateInstructionCount() there instead.
 *
 * This header pulls in <linux/perf_event.h>, so include it only where it is needed
 * rather than from a widely-included header.
 */

#ifndef __PerfInstructions__
#define __PerfInstructions__

#include "Lib/Portability.hpp"

#if VAMPIRE_PERF_EXISTS
#include <cstdint>
#include <linux/perf_event.h>
#endif

namespace Lib {
namespace Timer {

#if VAMPIRE_PERF_EXISTS

/** The mmap'd metadata page of the perf event, or nullptr when unavailable.
 *  Set up by Timer::reinitialise(). */
extern perf_event_mmap_page *PERF_MMAP_PAGE;

/** Whether instructionCount() can return anything meaningful at all. */
bool instructionCountingAvailable();

#if defined(__x86_64__) || defined(__i386__)
inline uint64_t rdpmc(uint32_t counter)
{
  uint32_t low, high;
  __asm__ __volatile__("rdpmc" : "=a"(low), "=d"(high) : "c"(counter));
  return (static_cast<uint64_t>(high) << 32) | low;
}
#define VAMPIRE_RDPMC_EXISTS 1
#endif

#endif // VAMPIRE_PERF_EXISTS

/**
 * User-space instructions retired by this thread since the counter was reset,
 * or -1 if that cannot be determined right now.
 *
 * Callers should treat -1 as "no measurement", not as a count.
 */
inline long long instructionCount()
{
#if VAMPIRE_PERF_EXISTS && defined(VAMPIRE_RDPMC_EXISTS)
  perf_event_mmap_page *pc = PERF_MMAP_PAGE;
  if (!pc)
    return -1;

  uint64_t count;
  uint32_t seq, idx;
  int64_t offset;
  uint16_t width;

  do {
    // pc->lock is a seqlock the kernel bumps whenever it reschedules the event,
    // which is exactly when index and offset change under us
    seq = pc->lock;
    __atomic_signal_fence(__ATOMIC_SEQ_CST);

    idx = pc->index;      // 0: the event is not on this CPU's PMU at the moment
    offset = pc->offset;  // what it counted during previous schedulings
    width = pc->pmc_width;

    if (!pc->cap_user_rdpmc || !idx || width == 0 || width > 64)
      return -1;

    count = rdpmc(idx - 1);
    // the hardware register is narrower than 64 bits (typically 48); sign-extend
    count <<= 64 - width;
    count = static_cast<uint64_t>(static_cast<int64_t>(count) >> (64 - width));
    count += offset;

    __atomic_signal_fence(__ATOMIC_SEQ_CST);
  } while (pc->lock != seq);

  return static_cast<long long>(count);
#else
  return -1;
#endif
}

} // namespace Timer
} // namespace Lib

#endif // __PerfInstructions__
