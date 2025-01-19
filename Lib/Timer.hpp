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
 *  @file Timer.hpp
 *  Defines class Timer
 *  @since 12/04/2006
 */

#ifndef __Timer__
#define __Timer__

#include <ostream>
#include <string>

namespace Lib {
namespace Timer {
  // (re)initialise the timer - from this point onwards:
  // 1. resource limits are enforced, unless `disableLimitEnforcement();`
  // 2. elapsed time (instructions) data should be live
  //
  // should be called exactly once per process as it internally spawns a std::thread
  void reinitialise();

  // disables exit on resource out: call when a proof has been found!
  // permanently disabled per-process
  // blocks if a resource limit was already reached and we are exiting
  void disableLimitEnforcement();

  // elapsed time
  long elapsedMilliseconds();
  inline long elapsedDeciseconds()
  { return elapsedMilliseconds() / 100; }

  // output times in various formats (?!)
  void printMSString(std::ostream &, int);
  std::string msToSecondsString(int);

  // instruction limiting stuff below - no-op if !VAMPIRE_PERF_EXISTS
  // whether instruction limiting succeeded
  bool instructionLimitingInPlace();
  // elapsed instructions
  long long elapsedInstructions();
  long elapsedMegaInstructions();

  // make sure that the instruction data is as up-to-date as possible
  // otherwise may be (slightly) stale
  void updateInstructionCount();
};
}

#endif /* __Timer__ */
