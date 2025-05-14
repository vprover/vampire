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
#include "Lib/VirtualIterator.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"

#include "LRS.hpp"

#define DETERMINISE_LRS_SAVE 0
#define DETERMINISE_LRS_LOAD 0

#if DETERMINISE_LRS_SAVE || DETERMINISE_LRS_LOAD
#include <fstream>
#endif

namespace Saturation
{

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;


void LRS::poppedFromUnprocessed(Clause* c)
{
  if(shouldUpdateLimits()) {
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
bool LRS::shouldUpdateLimits()
{
  if (env.statistics->activations <= 10)
    return false;

  static unsigned cnt=0;
  cnt++;

  //when there are limits, we check more frequently so we don't skip too much inferences
  if(cnt==500 || (_passive->limitsActive() && cnt>50 ) ) {
    cnt=0;
    return true;
  }
  return false;
}

/**
 * Return an estimate of the number of clauses that the saturation
 * algorithm will be able to activate in the remaining time
 */
long long LRS::estimatedReachableCount()
{
#if DETERMINISE_LRS_LOAD
  static std::ifstream infile("lrs_data.txt");
  long long thing;
  if (infile >> thing) {
    cout << "reading " << thing << endl;
    return thing;
  }
#endif

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

#if DETERMINISE_LRS_SAVE
  static std::ofstream outfile("lrs_data.txt");
  outfile << result << endl;
#endif

  return result;
}

}
