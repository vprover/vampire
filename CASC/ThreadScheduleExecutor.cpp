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
#include <condition_variable>

#define DECI(milli) (milli/100)

namespace CASC {
bool ThreadScheduleExecutor::run(const Schedule &schedule)
{
  CALL("ThreadScheduleExecutor::run");

  const int num_threads = 8;
  std::thread threads[num_threads]{};
  // if the thread in question is running or not
  std::atomic<bool> busy[num_threads]{};
  // basically a nasty counting semaphore, but we don't have one until C++20
  std::condition_variable task_done;
  std::mutex task_mutex;
  int tasks_idle = 0;

  // this closure is run _by_ a thread...
  auto parent_signature = env.signature;
  auto parent_sharing = env.sharing;
  auto parent_options = env.options;
  auto task = [&](vstring code, int remainingTime, unsigned i) {
    // copy options from parent thread
    *env.options = *parent_options;
    // also deep-copy the signature
    env.signature->clone_from(parent_signature);
    // but we can share the term sharing (!)
    // keep a copy of the original to avoid a double-free though
    auto sharing = env.sharing;
    env.sharing = parent_sharing;
    // thread setup done, now do All The Things
    _executor->runSlice(code, remainingTime);
    // swap the term sharing back in
    env.sharing = sharing;
    // indicate we're done
    std::lock_guard<std::mutex> task_lock(task_mutex);
    tasks_idle++;
    busy[i] = false;
    task_done.notify_one();
    std::cout << "finished" << std::endl;
  };

  // ...but this closure _starts_ the thread
  Schedule::BottomFirstIterator it(schedule);
  int remainingTime = DECI(env.remainingTime());
  auto launch_task = [&](int i) {
      vstring code = it.next();
      busy[i] = true;
      {
        BYPASSING_ALLOCATOR;
        threads[i] = std::thread(task, code, remainingTime, i);
      }
  };

  // start some threads so we can wait on them
  for(int i = 0; i < num_threads && it.hasNext(); i++) {
    launch_task(i);
  }

  // while we have time, wait for threads to finish and spawn new ones
  while(
    Timer::syncClock(),
    remainingTime = DECI(env.remainingTime()),
    remainingTime > 0 && it.hasNext()
  ) {
    std::unique_lock<std::mutex> task_lock(task_mutex);
    task_done.wait(task_lock, [&]() { return tasks_idle > 0; });
    tasks_idle--;
    for(int i = 0; i < num_threads; i++) {
      if(!busy[i]) {
        if(threads[i].joinable())
          threads[i].join();
        if(it.hasNext())
          launch_task(i);
        break;
      }
    }
  }

  // cleanup after time runs out
  for(int i = 0; i < num_threads; i++) {
    if(threads[i].joinable())
      threads[i].join();
  }

  return false;
}
} //namespace CASC
#endif
