#pragma once

#define BENCH_TOD_PERFORMANCES 1
#define BENCH_STATS 1
#define USE_INSTR_COUNT 1

#if BENCH_TOD_PERFORMANCES
#if VAMPIRE_PERF_EXISTS && USE_INSTR_COUNT
#include <linux/perf_event.h>
#endif
#include "BenchUtils.hpp"

#include <iostream>


namespace bench {
  class TODCounter {
    public:
      TODCounter() = default;
      ~TODCounter() = default;

      inline void startFullProcedure() {
        _fullProcedureCounter.startAndHold();
        _fullProcedureNumber++;
        _fullProcedureCounter.resume();
      }
      inline void stopFullProcedure(){
        _fullProcedureCounter.stop();
      }
      inline void startPreProcess(){
        _preProcessCounter.startAndHold();
        _preProcessNumber++;
        _preProcessCounter.resume();
      }
      inline void stopPreProcess(){
        _preProcessCounter.stop();
      }
      inline void startComparison(){
        _comparisonCounter.startAndHold();
        _comparisonNumber++;
        _comparisonCounter.resume();
      }
      inline void stopComparison(){
        _comparisonCounter.stop();
      }
      inline void startPositivityCheck(){
        _positivityCheckCounter.startAndHold();
        _positivityCheckNumber++;
        _positivityCheckCounter.resume();
      }
      inline void stopPositivityCheck(){
        _positivityCheckCounter.stop();
      }

      inline void bumpCreatedNodes(){
        _blocker.start();
        _numberOfCreatedNodes++;
        _blocker.stop();
      }
      inline void bumpProcessedNodes(){
        _blocker.start();
        _numberOfProcessedNodes++;
        _blocker.stop();
      }
      inline void bumpUsedNodes(){
        _blocker.start();
        _numberOfUsedNodes++;
        _blocker.stop();
      }

      inline long long getTotalFullProcedureCount() {
        return _fullProcedureCounter.getTotalInstrCount();
      }
      inline long long getTotalPreProcessCount() {
        return _preProcessCounter.getTotalInstrCount();
      }
      inline long long getTotalComparisonCount() {
        return _comparisonCounter.getTotalInstrCount();
      }
      inline long long getTotalPositivityCheckCount() {
        return _positivityCheckCounter.getTotalInstrCount();
      }

      inline long getNumberOfCreatedNodes() {
        return _numberOfCreatedNodes;
      }
      inline long getNumberOfProcessedNodes() {
        return _numberOfProcessedNodes;
      }
      inline long getNumberOfUsedNodes() {
        return _numberOfUsedNodes;
      }

      void print() {
        std::cout << "Executed " << _fullProcedureNumber << " full procedures in total with " << getTotalFullProcedureCount() << " instructions." << std::endl;
        std::cout << "Executed " << _preProcessNumber << " pre-processes in total with " << getTotalPreProcessCount() << " instructions." << std::endl;
        std::cout << "Executed " << _comparisonNumber << " comparisons in total with " << getTotalComparisonCount() << " instructions." << std::endl;
        std::cout << "Executed " << _positivityCheckNumber << " positivity checks in total with " << getTotalPositivityCheckCount() << " instructions." << std::endl;
        std::cout << "Created " << _numberOfCreatedNodes << " nodes." << std::endl;
        std::cout << "Processed " << _numberOfProcessedNodes << " nodes." << std::endl;
        std::cout << "Used " << _numberOfUsedNodes << " nodes." << std::endl;
      }

    private:
      InstrCounter _fullProcedureCounter;
      long _fullProcedureNumber = 0;

      InstrCounter _preProcessCounter;
      long _preProcessNumber = 0;

      InstrCounter _comparisonCounter;
      long _comparisonNumber = 0;

      InstrCounter _positivityCheckCounter;
      long _positivityCheckNumber = 0;

      // The blocker is used to prevent the other counters from measuring extra statistics
      InstrCounter _blocker;
      long _numberOfCreatedNodes = 0;
      long _numberOfProcessedNodes = 0;
      long _numberOfUsedNodes = 0;
  };
}

#endif
