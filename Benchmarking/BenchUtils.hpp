#pragma once

#if VAMPIRE_PERF_EXISTS
#include <linux/perf_event.h>
#endif
#include <chrono>

namespace bench {
  struct InstrCounter {
  public:
    InstrCounter();
    ~InstrCounter();
    static void setInstructionLimit(long long limit);
    static bool limitReached();
    void start();
    void stop();

    long long getTotalInstrCount();
    void reset();

  private:
    inline bool running() { return _startCount != -1; }
    long long _startCount = -1;
    long long _totalInstrCount = 0;
    long long _lastOverHead = 0;
  };

  struct TimeCounter {
  public:
    TimeCounter();
    ~TimeCounter();
    void start();
    void stop();
    long long getTotalTime();
  private:
    long long _startTime = 0;
    long long _totalTime = 0;
  };

  void startVampire();
  void stopVampire();
  long long getVampireCount();
}
