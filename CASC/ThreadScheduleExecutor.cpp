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
    {
      BYPASSING_ALLOCATOR;
      std::thread t([&] {
        _executor->runSlice(code, remainingTime);
      });
      t.join();
    }
    Timer::syncClock();
  }

  return success;
}
} //namespace CASC
#endif
