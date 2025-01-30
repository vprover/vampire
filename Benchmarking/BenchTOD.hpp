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
  static InstrCounter demodulationCounter;
  static InstrCounter queryCounter;
  static InstrCounter preProcessCounter;
  static InstrCounter comparisonCounter;
  static InstrCounter positivityCheckCounter;
  // The blocker is used to prevent the other counters from measuring extra statistics
  static InstrCounter blockCounter;
  class TODCounter {
    public:
      TODCounter() = default;
      ~TODCounter() = default;

      static inline void startFwDemodulation() {
        demodulationCounter.start();
      }
      static inline void stopFwDemodulation(){
        demodulationCounter.stop();
      }
      static long long getTotalFwDemodulationCount() {
        return demodulationCounter.getTotalInstrCount();
      }

      static inline void startTODQuery() {
        queryCounter.startAndHold();
        env.statistics->todQueries++;
        std::cout << "startTODQuery" << std::endl;
        std::cout << "Number of instructions so far " << getInstrTodQuery() << std::endl;
        queryCounter.resume();
      }
      static inline void stopTODQuery(){
        queryCounter.stop();
      }
      static inline long long getInstrTodQuery() {
        return queryCounter.getTotalInstrCount();
      }

      static inline void startPreProcess(){
        preProcessCounter.startAndHold();
        env.statistics->todPreprocesses++;
        preProcessCounter.resume();
      }
      static inline void stopPreProcess(){
        preProcessCounter.stop();
      }
      static inline long long getInstrPreProcess() {
        return preProcessCounter.getTotalInstrCount();
      }

      static inline void startOrderingCheck(){
        comparisonCounter.startAndHold();
        env.statistics->todOrderingChecks++;
        comparisonCounter.resume();
      }
      static inline void stopOrderingCheck(){
        comparisonCounter.stop();
      }
      static inline long long getInstrOrederinCheck() {
        return comparisonCounter.getTotalInstrCount();
      }

      static inline void startPositivityCheck(){
        positivityCheckCounter.startAndHold();
        env.statistics->todPositivityChecks++;
        positivityCheckCounter.resume();
      }
      static inline void stopPositivityCheck(){
        positivityCheckCounter.stop();
      }
      static inline long long getInstrPositivityCheckCount() {
        return positivityCheckCounter.getTotalInstrCount();
      }

      static inline void bumpCreatedNodes(){
        blockCounter.start();
        env.statistics->todNodesCreated++;
        blockCounter.stop();
      }
      static inline void bumpUsedNodes(){
        blockCounter.start();
        env.statistics->todNodesUsed++;
        blockCounter.stop();
      }


  };
}

#endif
