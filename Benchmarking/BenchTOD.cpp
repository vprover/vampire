#include "BenchTOD.hpp"
#include "Lib/Environment.hpp"
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

  void TODCounter::startFwDemodulation() {
    demodulationCounter.start();
  }
  void TODCounter::stopFwDemodulation(){
    demodulationCounter.stop();
  }
  long long TODCounter::getTotalFwDemodulationCount() {
    return demodulationCounter.getTotalInstrCount();
  }

  void TODCounter::startTODQuery() {
    queryCounter.startAndHold();
    Lib::env.statistics->todQueries++;
    // std::cout << "startTODQuery" << std::endl;
    // std::cout << "Number of instructions so far " << getInstrTodQuery() << std::endl;
    queryCounter.resume();
  }
  void TODCounter::stopTODQuery(){
    queryCounter.stop();
  }
  long long TODCounter::getInstrTodQuery() {
    return queryCounter.getTotalInstrCount();
  }

  void TODCounter::startPreProcess(){
    preProcessCounter.startAndHold();
    env.statistics->todPreprocesses++;
    preProcessCounter.resume();
  }
  void TODCounter::stopPreProcess(){
    preProcessCounter.stop();
  }
  long long TODCounter::getInstrPreProcess() {
    return preProcessCounter.getTotalInstrCount();
  }

  void TODCounter::startOrderingCheck(){
    comparisonCounter.startAndHold();
    env.statistics->todOrderingChecks++;
    comparisonCounter.resume();
  }
  void TODCounter::stopOrderingCheck(){
    comparisonCounter.stop();
  }
  long long TODCounter::getInstrOrederinCheck() {
    return comparisonCounter.getTotalInstrCount();
  }

  void TODCounter::startPositivityCheck(){
    positivityCheckCounter.startAndHold();
    env.statistics->todPositivityChecks++;
    positivityCheckCounter.resume();
  }
  void TODCounter::stopPositivityCheck(){
    positivityCheckCounter.stop();
  }
  long long TODCounter::getInstrPositivityCheckCount() {
    return positivityCheckCounter.getTotalInstrCount();
  }

  void TODCounter::bumpCreatedNodes(){
    blockCounter.start();
    env.statistics->todNodesCreated++;
    blockCounter.stop();
  }
  void TODCounter::bumpUsedNodes(){
    blockCounter.start();
    env.statistics->todNodesUsed++;
    blockCounter.stop();
  }
}
