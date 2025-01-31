#pragma once

#define BENCH_TOD_PERFORMANCES 1
#define BENCH_STATS 1
#define USE_INSTR_COUNT 1

#if BENCH_TOD_PERFORMANCES
#if VAMPIRE_PERF_EXISTS && USE_INSTR_COUNT
#include <linux/perf_event.h>
#endif
#include "BenchUtils.hpp"
#include "Shell/Statistics.hpp"

#include <iostream>


namespace bench {
  class TODCounter {
    public:
      TODCounter() = delete;
      ~TODCounter() = delete;

      static void startFwDemodulation();
      static void stopFwDemodulation();
      static long long getTotalFwDemodulationCount();

      static void startTODQuery();
      static void stopTODQuery();
      static long long getInstrTodQuery();

      static void startPreProcess();
      static void stopPreProcess();
      static long long getInstrPreProcess();

      static void startOrderingCheck();
      static void stopOrderingCheck();
      static long long getInstrOrederinCheck();

      static void startPositivityCheck();
      static void stopPositivityCheck();
      static long long getInstrPositivityCheckCount();

      static void bumpCreatedNodes();
      static void bumpUsedNodes();
  };
}

#endif
