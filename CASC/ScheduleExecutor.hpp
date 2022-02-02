/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __ScheduleExecutor__
#define __ScheduleExecutor__

#include <unistd.h>
#include "Schedules.hpp"

namespace CASC
{

class ProcessPriorityPolicy
{
public:
  virtual float staticPriority(Lib::vstring sliceCode) = 0;
  virtual float dynamicPriority(pid_t pid) = 0;
};

class SliceExecutor
{
public:
  [[noreturn]] virtual void runSlice(Lib::vstring sliceCode, int remaminingTime) = 0;
};

class ScheduleExecutor
{
public:
  ScheduleExecutor(ProcessPriorityPolicy *policy, SliceExecutor *executor);
  bool run(const Schedule &schedule);

private:
  pid_t spawn(Lib::vstring code, int remaminingTime);
  unsigned getNumWorkers();

  ProcessPriorityPolicy *_policy;
  SliceExecutor *_executor;
  unsigned _numWorkers;
};
}

#endif
