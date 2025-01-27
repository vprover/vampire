#pragma once

#if VAMPIRE_PERF_EXISTS
#include <linux/perf_event.h>
#endif
#include <chrono>

namespace bench {
  class InstrCounter {
  public:
    InstrCounter();
    ~InstrCounter();
    void start();
    void stop();

    void startAndHold();
    void stopAndHold();
    void resume();

    long long getTotalInstrCount();
    void reset();

  private:
    inline bool running() { return _startCount != -1; }
    long long _startCount = -1;
    long long _totalInstrCount = 0;
  };

  class TimeCounter {
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
