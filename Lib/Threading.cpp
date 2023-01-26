#if VTHREADED
#include <thread>
const std::thread::id MAIN_THREAD_ID = std::this_thread::get_id();

bool weAreTheMainThread() {
  // not initialised yet, we're in startup
  if(MAIN_THREAD_ID == std::thread::id())
    return true;

  return std::this_thread::get_id() == MAIN_THREAD_ID;
}
#endif
