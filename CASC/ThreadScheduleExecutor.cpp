/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#if VTHREADED
#include "ThreadScheduleExecutor.hpp"

#include "Kernel/Signature.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"

#include <thread>

#define DECI(milli) (milli/100)

namespace CASC {
bool ThreadScheduleExecutor::run(const Schedule &schedule)
{
  CALL("ThreadScheduleExecutor::run");
  bool success = false;
  // TODO is this the right way up?
  // It matches the process executor but looks wrong
  Schedule::BottomFirstIterator it(schedule);

  int remainingTime;
  while(
    Timer::syncClock(),
    remainingTime = DECI(env.remainingTime()),
    remainingTime > 0 &&
    it.hasNext()
  ) {
    vstring code = it.next();
    auto parent_signature = env.signature;
    auto parent_sharing = env.sharing;
    auto parent_options = env.options;
    auto task = [&] {
      *env.options = *parent_options;
      env.signature->clone_from(parent_signature);
      auto sharing = env.sharing;
      env.sharing = parent_sharing;
      _executor->runSlice(code, remainingTime);
      env.sharing = sharing;
    };
    {
      BYPASSING_ALLOCATOR;
      const int num_threads = 8;
      std::thread threads[num_threads];
      for(int i = 0; i < num_threads; i++)
        threads[i] = std::thread(task);
      for(int i = 0; i < num_threads; i++)
        threads[i].join();
    }
  }

  return success;
}
} //namespace CASC
#endif
