#include "BenchTOD.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Kernel/OrderingComparator.hpp"

#include <iostream>

namespace bench {

  static double updateVariance(double var, double average, double newSample, unsigned nSamples) {
    double diff = average - newSample;
    return (var * nSamples + (diff * diff)) / (nSamples + 1);
  }

#if BENCH_TOD_INSTR_COUNT
#if BENCH_TOD_FW_DEMODULATION
  static InstrCounter demodulationCounter;
#endif
#if BENCH_TOD_QUERIES
  static InstrCounter queryCounter;
#endif
#if BENCH_TOD_PREPROCESS
  static InstrCounter preProcessCounter;
#endif
#if BENCH_TOD_ORDERING_CHECKS
  static InstrCounter orderingCheckCounter;
#endif
#if BENCH_TOD_POSITIVITY_CHECKS
  static InstrCounter positivityCheckCounter;
#endif
#endif

#if BENCH_TOD_TIME
  static TimeCounter demodulationTimer;
  static unsigned nSamples = 0;
  static long long lastTotTimeDemo = 0;
  static double varDemo;

#if BENCH_TOD_QUERIES
  static TimeCounter queryTimer;
#endif
#if BENCH_TOD_PREPROCESS
  static TimeCounter preProcessTimer;
#endif
#if BENCH_TOD_ORDERING_CHECKS
  static TimeCounter orderingCheckTimer;
#endif
#if BENCH_TOD_POSITIVITY_CHECKS
  static TimeCounter positivityCheckTimer;
#endif
#endif

void TODCounter::startFwDemodulation() {
#if BENCH_TOD_FW_DEMODULATION
#if BENCH_TOD_TIME
    demodulationTimer.start();
#endif
#if BENCH_TOD_INSTR_COUNT
    demodulationCounter.start();
#endif
#endif
  }

  void TODCounter::stopFwDemodulation() {
#if BENCH_TOD_FW_DEMODULATION
#if BENCH_TOD_INSTR_COUNT
    demodulationCounter.stop();
#endif
#if BENCH_TOD_TIME
    demodulationTimer.stop();
    long long totTimeDemo = demodulationTimer.getTotalTime();
    varDemo = updateVariance(varDemo,
                             totTimeDemo / (nSamples + 1),
                             totTimeDemo - lastTotTimeDemo,
                             nSamples);
    nSamples++;
    lastTotTimeDemo = totTimeDemo;
#endif
#endif
  }

  long long TODCounter::getFwDemodulationCount() {
#if BENCH_TOD_FW_DEMODULATION && BENCH_TOD_INSTR_COUNT
    return demodulationCounter.getTotalInstrCount();
#else
    return 0;
#endif
  }

  long long TODCounter::getFwDemodulationTime() {
#if BENCH_TOD_FW_DEMODULATION && BENCH_TOD_TIME
    return demodulationTimer.getTotalTime();
#else
    return 0;
#endif
  }

  double TODCounter::getVarianceFwemodulation() {
#if BENCH_TOD_FW_DEMODULATION && BENCH_TOD_TIME
    return varDemo;
#else
    return 0.0;
#endif
  }


  void TODCounter::startTODQuery() {
    env.statistics->todQueries++;
#if BENCH_TOD_QUERIES
#if BENCH_TOD_TIME
    queryTimer.start();
#endif
#if BENCH_TOD_INSTR_COUNT
    queryCounter.start();
#endif
#endif
  }

  void TODCounter::stopTODQuery() {
#if BENCH_TOD_QUERIES
#if BENCH_TOD_INSTR_COUNT
    queryCounter.stop();
#endif
#if BENCH_TOD_TIME
    queryTimer.stop();
#endif
#endif
  }

  long long TODCounter::getTodQueryTime() {
#if BENCH_TOD_QUERIES && BENCH_TOD_TIME
    return queryTimer.getTotalTime();
#else
    return 0;
#endif
  }

  long long TODCounter::getTodQueryCount() {
#if BENCH_TOD_QUERIES && BENCH_TOD_INSTR_COUNT
    return queryCounter.getTotalInstrCount();
#else
    return 0;
#endif
  }

  void TODCounter::startPreProcess()
  {
    env.statistics->todPreprocesses++;
#if BENCH_TOD_PREPROCESS
#if BENCH_TOD_TIME
    preProcessTimer.start();
#endif
#if BENCH_TOD_INSTR_COUNT
    preProcessCounter.start();
#endif
#endif
  }

  void TODCounter::stopPreProcess() {
#if BENCH_TOD_PREPROCESS
#if BENCH_TOD_INSTR_COUNT
    preProcessCounter.stop();
#endif
#if BENCH_TOD_TIME
    preProcessTimer.stop();
#endif
#endif
  }

  long long TODCounter::getPreProcessTime() {
#if BENCH_TOD_PREPROCESS && BENCH_TOD_TIME
    return preProcessTimer.getTotalTime();
#else
    return 0;
#endif
  }

  long long TODCounter::getPreProcessCount() {
#if BENCH_TOD_PREPROCESS && BENCH_TOD_INSTR_COUNT
    return preProcessCounter.getTotalInstrCount();
#else
    return 0;
#endif
  }

  void TODCounter::startOrderingCheck()
  {
    env.statistics->todOrderingChecks++;
#if BENCH_TOD_ORDERING_CHECKS
#if BENCH_TOD_TIME
    orderingCheckTimer.start();
#endif
#if BENCH_TOD_INSTR_COUNT
    orderingCheckCounter.start();
#endif
#endif
  }

  void TODCounter::stopOrderingCheck() {
#if BENCH_TOD_ORDERING_CHECKS
#if BENCH_TOD_INSTR_COUNT
    orderingCheckCounter.stop();
#endif
#if BENCH_TOD_TIME
    orderingCheckTimer.stop();
#endif
#endif
  }

  long long TODCounter::getOrderingCheckTime() {
#if BENCH_TOD_ORDERING_CHECKS && BENCH_TOD_TIME
    return orderingCheckTimer.getTotalTime();
#else
    return 0;
#endif
  }

  long long TODCounter::getOrderingCheckCount() {
#if BENCH_TOD_ORDERING_CHECKS && BENCH_TOD_INSTR_COUNT
    return orderingCheckCounter.getTotalInstrCount();
#else
    return 0;
#endif
  }


  void TODCounter::startPositivityCheck()
  {
    env.statistics->todPositivityChecks++;
#if BENCH_TOD_POSITIVITY_CHECKS
#if BENCH_TOD_TIME
    positivityCheckTimer.start();
#endif
#if BENCH_TOD_INSTR_COUNT
    positivityCheckCounter.start();
#endif
#endif
  }

  void TODCounter::stopPositivityCheck() {
#if BENCH_TOD_POSITIVITY_CHECKS
#if BENCH_TOD_INSTR_COUNT
    positivityCheckCounter.stop();
#endif
#if BENCH_TOD_TIME
    positivityCheckTimer.stop();
#endif
#endif
  }

  long long TODCounter::getPositivityCheckTime() {
#if BENCH_TOD_POSITIVITY_CHECKS && BENCH_TOD_TIME
    return positivityCheckTimer.getTotalTime();
#else
    return 0;
#endif
  }

  long long TODCounter::getPositivityCheckCount() {
#if BENCH_TOD_POSITIVITY_CHECKS && BENCH_TOD_INSTR_COUNT
    return positivityCheckCounter.getTotalInstrCount();
#else
    return 0;
#endif
  }

  void TODCounter::bumpCreatedNodes()
  {
    env.statistics->todNodesCreated++;
  }
  void TODCounter::bumpUsedNodes()
  {
    env.statistics->todNodesUsed++;
  }
  void TODCounter::bumpDeletedNodes()
  {
    env.statistics->todNodesDeleted++;
  }
  void TODCounter::bumpTermNodes()
  {
    env.statistics->todTermNodesAtEnd++;
    env.statistics->todTermNodesCreated++;
  }
  void TODCounter::bumpDataNodes()
  {
    env.statistics->todDataNodesAtEnd++;
    env.statistics->todDataNodesCreated++;
  }
  void TODCounter::bumpPolyNodes()
  {
    env.statistics->todPolyNodesAtEnd++;
    env.statistics->todPolyNodesCreated++;
  }
}
