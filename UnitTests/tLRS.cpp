/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/Problem.hpp"
#include "Saturation/LRS.hpp"
#include "Shell/Options.hpp"
#include "Test/UnitTesting.hpp"

using namespace Kernel;
using namespace Shell;

namespace {
class ReplayLRS : public Saturation::LRS {
public:
  using LRS::LRS;
  using LRS::shouldUpdateLimits;
  using LRS::estimatedReachableCount;
};

void checkReplay(unsigned pops)
{
  Problem problem;
  Options options;
  options.set("lrs_load_trace_file", ABSOLUTE_SOURCE_DIR "/UnitTests/lrs-replay.trace");
  options.resolveAwayAutoValues(problem);
  ReplayLRS lrs(problem, options);

  ASS(!lrs.shouldUpdateLimits(pops));
  ASS(!lrs.shouldUpdateLimits(0));
  ASS(lrs.shouldUpdateLimits(0));
  ASS_EQ(lrs.estimatedReachableCount(), 17);
  ASS(!lrs.shouldUpdateLimits(pops));
  ASS(lrs.shouldUpdateLimits(0));
  ASS_EQ(lrs.estimatedReachableCount(), -1);
  ASS(lrs.shouldUpdateLimits(0));
  ASS_EQ(lrs.estimatedReachableCount(), 3);
  ASS(!lrs.shouldUpdateLimits(pops));
  ASS(!lrs.shouldUpdateLimits(pops));
}
}

TEST_FUN(replay_waits_for_recorded_loop_after_pops)
{
  checkReplay(501);
}

TEST_FUN(replay_counts_consecutive_empty_loops)
{
  checkReplay(0);
}

TEST_FUN(replay_rejects_ambiguous_pop_count_format)
{
  Problem problem;
  Options options;
  options.set("lrs_load_trace_file", ABSOLUTE_SOURCE_DIR "/UnitTests/lrs-replay-legacy.trace");
  options.resolveAwayAutoValues(problem);
  ReplayLRS lrs(problem, options);
  try {
    lrs.shouldUpdateLimits(501);
  } catch (Lib::UserErrorException& error) {
    ASS_NEQ(error.msg().find("record a new trace"), std::string::npos);
    return;
  }
  ASSERTION_VIOLATION;
}
