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
  virtual void runSlice(Lib::vstring sliceCode, int terminationTime) NO_RETURN = 0;
};

class ScheduleExecutor
{
public:
  ScheduleExecutor(ProcessPriorityPolicy *policy, SliceExecutor *executor);
  bool run(const Schedule &schedule, int terminationTime);

private:
  pid_t spawn(Lib::vstring code, int terminationTime);
  unsigned getNumWorkers();

  ProcessPriorityPolicy *_policy;
  SliceExecutor *_executor;
  unsigned _numWorkers;
};
}

#endif
