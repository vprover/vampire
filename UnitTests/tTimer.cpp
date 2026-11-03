/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <chrono>
#include <cstdlib>
#include <thread>

#include "Lib/Environment.hpp"
#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Timer.hpp"
#include "Shell/Options.hpp"
#include "Test/UnitTesting.hpp"

using namespace Lib;
using namespace std::chrono_literals;

namespace {
// The timer thread cannot be stopped, so each test starts it in a child process.
void inFreshProcess(void (*test)(), int expectedExitCode = 0)
{
  auto child = Sys::fork();
  if (child == 0) {
    test();
    std::exit(0);
  }
  auto result = Sys::waitForChildTermination(child);
  ASS(!result.signalled);
  ASS_EQ(result.code, expectedExitCode);
}
}

// The timer can outlive env.options during global cleanup (#979).
TEST_FUN(does_not_read_options_after_start)
{
  inFreshProcess([] {
    env.options->setTimeLimitInDeciseconds(0);
    Timer::reinitialise(false);
    auto* options = env.options;
    env.options = nullptr;
    std::this_thread::sleep_for(25ms);
    env.options = options;
  });
}

TEST_FUN(enforces_time_limit)
{
  inFreshProcess([] {
    env.options->setTimeLimitInDeciseconds(1);
    Timer::reinitialise(false);
    std::this_thread::sleep_for(2s);
  }, 1);
}
