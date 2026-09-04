/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file LRS.cpp
 * Implements class LRS.
 */

#include <chrono>

#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Kernel/Clause.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"

#include "LRS.hpp"


namespace Saturation
{

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;


void LRS::afterUnprocessedLoop(unsigned popsElapsed)
{
  if(shouldUpdateLimits(popsElapsed)) {
    TIME_TRACE("LRS limit maintenance");

    // Charge this update against the maintenance budget. steady_clock rather than
    // Timer::elapsedMilliseconds(), because a typical update takes a few hundred
    // microseconds and would round to zero milliseconds.
    auto startedAt = std::chrono::steady_clock::now();
    long startInstrs = Timer::elapsedMegaInstructions();

    long long estimatedReachable=estimatedReachableCount();
    if(estimatedReachable>=0) {
      _passive->updateLimits(estimatedReachable);
    }

    _maintenanceMicros += std::chrono::duration_cast<std::chrono::microseconds>(
        std::chrono::steady_clock::now() - startedAt).count();
    // Note this one is coarse: elapsedMegaInstructions() returns a value the timer
    // thread refreshes on a 1ms tick, so a single update usually sees no change at
    // all and occasionally sees a jump. The tick advances at the true rate, so the
    // running total is what converges -- which is why the budget below is checked
    // cumulatively rather than per update.
    _maintenanceInstrs += Timer::elapsedMegaInstructions() - startInstrs;
  }
}

/**
 * Is the instruction limit the one that will stop this run first?
 *
 * estimatedReachableCount() takes the min of a time-based and an instruction-based
 * estimate, i.e. it is governed by whichever limit binds. The maintenance budget
 * follows the same rule, since the resource worth conserving is the one that runs
 * out first. With no instruction limit set, or no way to read the counter, it is
 * time by default.
 */
bool LRS::bindingResourceIsInstructions()
{
  long instrLimit = 0; // (in mega-instructions)
#if VAMPIRE_PERF_EXISTS
  instrLimit = _opt.simulatedInstructionLimit()
    ? _opt.simulatedInstructionLimit()
    : _opt.instructionLimit();
#endif
  if (instrLimit <= 0) {
    return false;
  }
  int timeLimitDeci = _opt.simulatedTimeLimit()
    ? _opt.simulatedTimeLimit()
    : _opt.timeLimitInDeciseconds();
  if (timeLimitDeci <= 0) {
    return true;
  }
  // both active: whichever is a larger fraction of the way to its limit
  long instrsBurned = Timer::elapsedMegaInstructions() - _lrsStartInstrs;
  long timeSpent = Timer::elapsedMilliseconds() - _lrsStartTime; // (in milliseconds)
  return instrsBurned * static_cast<long long>(timeLimitDeci) * 100 >
         timeSpent * static_cast<long long>(instrLimit);
}

/**
 * Has limit maintenance stayed inside its share of the saturation budget so far?
 *
 * Each update simulates the passive set, at a cost proportional to the number of
 * clauses it expects to still reach, so it gets more expensive as a run goes on.
 * Left alone it reaches 90% of the longest runs. Comparing the running cost against
 * the running total keeps the share near -lmb without needing to predict anything:
 * after an expensive update this simply stays false until saturation catches up.
 */
bool LRS::withinMaintenanceBudget()
{
  // double rather than float: on a long run the right-hand side reaches ~1e7
  // microseconds, which is where float's 24-bit mantissa starts losing units.
  double budget = _opt.lrsMaintenanceBudget();

  if (bindingResourceIsInstructions()) {
    long spent = Timer::elapsedMegaInstructions() - _lrsStartInstrs;
    return _maintenanceInstrs <= budget * spent;
  }
  long spent = Timer::elapsedMilliseconds() - _lrsStartTime; // (in milliseconds)
  return _maintenanceMicros <= budget * spent * 1000.0;
}

/**
 * Return true if it is time to update age and weight
 * limits of the LRS strategy
 *
 * The pops counter sets the rate, exactly as before; the budget check can only ever
 * hold an update back. So this is a pure throttle: where updates are cheap the budget
 * never binds and the cadence is master's, and only the expensive runs -- the ones
 * where maintenance had grown to a large share of the run -- see any difference.
 */
bool LRS::shouldUpdateLimits(unsigned popsElapsed)
{
  openTraceFiles();

  _leftoverPops += popsElapsed;

  if (replaying()) {
    // Replay must not consult the clock, the instruction counter or the budget:
    // that is the whole point of the trace, and it is what lets a run recorded
    // under one limit be replayed under another. The recorded pop counts are the
    // only thing driving the cadence here.
    if (_traceExhausted || !readNextRecord()) {
      return false;
    }
    if (_leftoverPops < _nextRecordPops) {
      return false;
    }
    _leftoverPops = 0;
    _haveNextRecord = false; // consumed by the update we are about to make
    return true;
  }

  if (env.statistics->activations <= 10)
    return false;

  //when there are limits, we check more frequently so we don't skip too much inferences
  if(_leftoverPops>500 || (_passive->limitsActive() && _leftoverPops>50 )) {
    if (!withinMaintenanceBudget()) {
      // Deliberately leave _leftoverPops standing, so that the update happens at the
      // first opportunity once the budget allows rather than after a further 50 pops.
      return false;
    }
    _popsAtFire = _leftoverPops;
    _leftoverPops = 0;
    return true;
  }
  return false;
}

/**
 * Ensure _nextRecordPops/_nextRecordResult hold the next unconsumed trace record.
 *
 * Returns false once the file runs out, after which no further updates are made:
 * finishing a replay on the live (clock-driven) logic would silently stop
 * reproducing the recorded run, which is worse than doing nothing.
 */
bool LRS::readNextRecord()
{
  if (_haveNextRecord) {
    return true;
  }
  if (*_loadTrace >> _nextRecordPops >> _nextRecordResult) {
    _haveNextRecord = true;
    return true;
  }
  if (!_traceExhausted) {
    _traceExhausted = true;
    addCommentSignForSZS(std::cout);
    std::cout << "LRS trace file exhausted; limits will no longer be updated"
              << std::endl;
  }
  return false;
}

/**
 * Open the trace files named by -lrs_save_trace_file / -lrs_load_trace_file, once.
 *
 * Lazily rather than in a constructor because LRS inherits Otter's constructors, and
 * because a run that sets neither option should not touch the filesystem at all.
 */
void LRS::openTraceFiles()
{
  if (_traceOpened) {
    return;
  }
  _traceOpened = true;

  const std::string& load = _opt.lrsLoadTraceFile();
  if (!load.empty()) {
    _loadTrace = std::make_unique<std::ifstream>(load.c_str());
  }
  const std::string& save = _opt.lrsSaveTraceFile();
  if (!save.empty()) {
    _saveTrace = std::make_unique<std::ofstream>(save.c_str());
  }
}

/**
 * Return an estimate of the number of clauses that the saturation
 * algorithm will be able to activate in the remaining time
 */
long long LRS::estimatedReachableCount()
{
  if (replaying()) {
    // shouldUpdateLimits only returns true here having consumed a record, so the
    // estimate to use is the one that record carried.
    return _nextRecordResult;
  }

  long currTime = Timer::elapsedMilliseconds();
  // time spent in saturation (parsing, preprocessing, and the initial loading up of the input into passive are excluded)
  long timeSpent=currTime-_lrsStartTime; // (in milliseconds)

  int opt_timeLimitDeci = _opt.timeLimitInDeciseconds();
  float correction_coef = _opt.lrsEstimateCorrectionCoef();
  int firstCheck=_opt.lrsFirstTimeCheck(); // (in percent)!

  long int opt_instruction_limit = 0; // (in mega-instructions)
#if VAMPIRE_PERF_EXISTS
  opt_instruction_limit = _opt.simulatedInstructionLimit()
    ? _opt.simulatedInstructionLimit()
    : _opt.instructionLimit();
#endif

  long currInstructions = Timer::elapsedMegaInstructions();
  long instrsBurned = currInstructions - _lrsStartInstrs;

  long long result = -1;

  if ((opt_timeLimitDeci > 0 && currTime < firstCheck*opt_timeLimitDeci) ||
      // the above, unit-wise: cf milliseconds on the left, and deci * percent on the right
      (opt_instruction_limit > 0 && currInstructions*100 < firstCheck*opt_instruction_limit)
  ) {
    goto finish;
  }

  {
    long long processed=env.statistics->activations;

    long long timeLeft; // (in milliseconds)
    if(_opt.simulatedTimeLimit()) {
      timeLeft=_opt.simulatedTimeLimit()*100 - currTime;
    } else {
      timeLeft=opt_timeLimitDeci*100 - currTime;
    }

    long int instrsLeft = opt_instruction_limit - instrsBurned;

    // note that result is -1 here already

    if(timeLeft > 0) {
      result = correction_coef*(processed*timeLeft)/timeSpent;
    } // otherwise, it's somehow past the deadline, or no timilimit set

    if (instrsLeft > 0) {
      long long res_by_instr = correction_coef*(processed*instrsLeft)/instrsBurned;
      if (result > 0) {
        result = std::min(result,res_by_instr);
      } else {
        result = res_by_instr;
      }
    } // otherwise, it's somehow past the deadline, or on instruction limit set
  }

  finish:

  if (_saveTrace) {
    (*_saveTrace) << _popsAtFire << " " << result << std::endl;
  }

  return result;
}

}
