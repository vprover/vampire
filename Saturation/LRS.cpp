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

#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Kernel/Clause.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"

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

    long long estimatedReachable=estimatedReachableCount();
    if(estimatedReachable>=0) {
      _passive->updateLimits(estimatedReachable);
    }
  }
}

/**
 * Return true if it is time to update age and weight
 * limits of the LRS strategy
 *
 * The time of the limit update is determined by a counter
 * of calls of this method.
 */
bool LRS::shouldUpdateLimits(unsigned popsElapsed)
{
  _leftoverPops += popsElapsed;

  if (env.statistics->activations <= 10)
    return false;

  //when there are limits, we check more frequently so we don't skip too much inferences
  if(_leftoverPops>500 || (_passive->limitsActive() && _leftoverPops>50 )) {
    _leftoverPops = 0;
    return true;
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
  openTraceFiles();

  if (_loadTrace) {
    long long thing;
    if (*_loadTrace >> thing) {
      return thing;
    }
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
    (*_saveTrace) << result << std::endl;
  }

  return result;
}

}
