#pragma once

#define BENCH_TOD_PERFORMANCES 1

#if BENCH_TOD_PERFORMANCES
#define BENCH_TOD_TIME 1
#define BENCH_TOD_INSTR_COUNT 1
#define BENCH_TOD_FW_DEMODULATION 1
#define BENCH_TOD_QUERIES 0
#define BENCH_TOD_PREPROCESS 0
#define BENCH_TOD_ORDERING_CHECKS 0
#define BENCH_TOD_POSITIVITY_CHECKS 0
#else
#define BENCH_TOD_TIME 0
#define BENCH_TOD_INSTR_COUNT 0
#define BENCH_TOD_FW_DEMODULATION 0
#define BENCH_TOD_QUERIES 0
#define BENCH_TOD_ORDERING_CHECKS 0
#define BENCH_TOD_POSITIVITY_CHECKS 0
#define USE_INSTR_COUNT 0
#endif

#include "BenchUtils.hpp"
#include "Shell/Statistics.hpp"

#include <iostream>

namespace bench {
  class TODCounter {
    private:

    public:
      TODCounter() = delete;
      ~TODCounter() = delete;

      static void startFwDemodulation();
      static void stopFwDemodulation();
      static long long getFwDemodulationCount();
      static long long getFwDemodulationTime();
      static double getVarianceFwemodulation();

      static void startTODQuery();
      static void stopTODQuery();
      static long long getTodQueryTime();
      static long long getTodQueryCount();

      static void startPreProcess();
      static void stopPreProcess();
      static long long getPreProcessTime();
      static long long getPreProcessCount();

      static void startOrderingCheck();
      static void stopOrderingCheck();
      static long long getOrderingCheckTime();
      static long long getOrderingCheckCount();

      static void startPositivityCheck();
      static void stopPositivityCheck();
      static long long getPositivityCheckTime();
      static long long getPositivityCheckCount();

      static void bumpCreatedNodes();
      static void bumpUsedNodes();
      static void bumpDeletedNodes();
      static void bumpTermNodes();
      static void bumpDataNodes();
      static void bumpPolyNodes();
  };
}
