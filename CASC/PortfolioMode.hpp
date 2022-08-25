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
 * @file PortfolioMode.hpp
 * Defines class PortfolioMode.
 */

#ifndef __PortfolioMode__
#define __PortfolioMode__

#include "Forwards.hpp"

#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "Lib/VString.hpp"
#include "Lib/Sys/Semaphore.hpp"

#include "Shell/Property.hpp"
#include "Schedules.hpp"

namespace CASC
{

using namespace Lib;
using namespace Shell;

class PortfolioMode {
  enum {
    SEM_LOCK = 0,
    SEM_PRINTED = 1
  };

  PortfolioMode();
public:
  static bool perform(float slowness);

  static void rescaleScheduleLimits(const Schedule& sOld, Schedule& sNew, float limit_multiplier);
  static void addScheduleExtra(const Schedule& sOld, Schedule& sNew, vstring extra);

private:
  // some of these names are kind of arbitrary and should be perhaps changed
  unsigned getSliceTime(const vstring &sliceCode);
  bool searchForProof();
  bool prepareScheduleAndPerform(const Shell::Property& prop);
  void getSchedules(const Property& prop, Schedule& quick, Schedule& fallback);

  bool runSchedule(Schedule schedule);
  bool runScheduleAndRecoverProof(Schedule schedule);
  [[noreturn]] void runSlice(vstring sliceCode, int remainingTime);
  [[noreturn]] void runSlice(Options& strategyOpt);

#if VDEBUG
  DHSet<pid_t> childIds;
#endif

  unsigned _numWorkers;
  float _slowness;

  const char * _tmpFileNameForProof;

  /**
   * Problem that is being solved.
   *
   * Note that in the current process this child object is the only one that
   * will be using the problem object.
   */
  ScopedPtr<Problem> _prb;

  Semaphore _syncSemaphore; // semaphore for synchronizing proof printing
};

}

#endif // __PortfolioMode__
