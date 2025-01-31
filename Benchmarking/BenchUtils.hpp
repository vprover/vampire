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
    void start() __attribute__((optimize(0)));
    void stop() __attribute__((optimize(0)));

    void startAndHold() __attribute__((optimize(0)));
    void stopAndHold() __attribute__((optimize(0)));
    void resume() __attribute__((optimize(0)));

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
}
