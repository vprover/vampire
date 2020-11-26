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
#include "Lib/TimeCounter.hpp"
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

using namespace Lib;
using namespace Kernel;
using namespace Shell;

bool LRS::isComplete()
{
  CALL("LRS::isComplete");

  return !_limitsEverActive && SaturationAlgorithm::isComplete();
}


void LRS::onUnprocessedSelected(Clause* c)
{
  CALL("LRS::onUnprocessedSelected");

  SaturationAlgorithm::onUnprocessedSelected(c);

  if(shouldUpdateLimits()) {
    TimeCounter tc(TC_LRS_LIMIT_MAINTENANCE);

    long long estimatedReachable=estimatedReachableCount();
    if(estimatedReachable>=0) {
      _passive->updateLimits(estimatedReachable);
      if(!_limitsEverActive) {
        _limitsEverActive=_passive->weightLimited() || _passive->ageLimited();
      }
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
  CALL("LRS::shouldUpdateLimits");

  static unsigned cnt=0;
  cnt++;

  //when there are limits, we check more frequently so we don't skip too much inferences
  if(cnt==500 || ((_passive->weightLimited() || _passive->ageLimited()) && cnt>50 ) ) {
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
  CALL("LRS::estimatedReachableCount");

#if DETERMINISE_LRS_LOAD
  static std::ifstream infile("lrs_data.txt");
  long long thing;
  if (infile >> thing) {
    cout << "reading " << thing << endl;
    return thing;
  }
#endif

  long long processed=env.statistics->activeClauses;
  int currTime=env.timer->elapsedMilliseconds();
  long long timeSpent=currTime-_startTime;
  //the result is in miliseconds, as _opt.lrsFirstTimeCheck() is in percents.
  int firstCheck=_opt.lrsFirstTimeCheck()*_opt.timeLimitInDeciseconds();
//  int timeSpent=currTime;

  long long result;

  if(timeSpent<firstCheck ) {
    result = -1;
    goto finish;
  }

  long long timeLeft;
  if(_opt.simulatedTimeLimit()) {
    timeLeft=_opt.simulatedTimeLimit()*100 - currTime;
  } else {
    timeLeft=_opt.timeLimitInDeciseconds()*100 - currTime;
  }
  if(timeLeft<=0 || processed<=10) {
    //we end-up here even if there is no time limit (i.e. time limit is set to 0)
    result = -1;
    goto finish;
  }

  result = (processed*timeLeft)/timeSpent;

  finish:

#if DETERMINISE_LRS_SAVE
  static std::ofstream outfile("lrs_data.txt");
  outfile << result << endl;
#endif

  return result;
}

}
