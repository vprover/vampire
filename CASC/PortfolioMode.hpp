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

#include "Lib/Portability.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"

#include "Lib/VString.hpp"
#include "Lib/Sys/Semaphore.hpp"

#include "Shell/Property.hpp"
#include "Schedules.hpp"
#include "ScheduleExecutor.hpp"

namespace CASC
{

using namespace std;
using namespace Lib;
using namespace Shell;

class PortfolioMode;

// Simple one-after-the-other priority.
class PortfolioProcessPriorityPolicy : public ProcessPriorityPolicy
{
public:
  float staticPriority(vstring sliceCode) override;
  float dynamicPriority(pid_t pid) override;
};

class PortfolioSliceExecutor : public SliceExecutor
{
public:
  PortfolioSliceExecutor(PortfolioMode *mode);
  void runSlice(vstring sliceCode, int remainingTime, int* fd) override;

private:
  PortfolioMode *_mode;
};

class PortfolioMode {
  enum {
    SEM_LOCK = 0,
    SEM_PRINTED = 1
  };

  #define WRITE 1

  PortfolioMode();
  friend void PortfolioSliceExecutor::runSlice(vstring sliceCode, int terminationTime, int* fd);
public:
  /**
   *  If no problem set, tries to read one from input file
   *  @param fd is a pipe used to return termination reason to API
   * */
  static bool perform(float slowness, Problem* prob = 0, int* fd = 0);
  unsigned getSliceTime(vstring sliceCode,vstring& chopped);

private:

  // some of these names are kind of arbitrary and should be perhaps changed

  bool searchForProof(Problem* prob = 0);
  bool performStrategy(Shell::Property* property);
  void getSchedules(Property& prop, Schedule& quick, Schedule& fallback);
  void getExtraSchedules(Property& prop, Schedule& old, Schedule& extra, bool add_extra, int time_multiplier); 
  bool runSchedule(Schedule& schedule);
  bool waitForChildAndCheckIfProofFound();
  [[noreturn]] void runSlice(vstring slice, unsigned timeLimitInDeciseconds, int* fd);
  [[noreturn]] void runSlice(Options& strategyOpt,  int* fd);

#if VDEBUG
  DHSet<pid_t> childIds;
#endif

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
