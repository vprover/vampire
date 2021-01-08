/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "ScheduleExecutor.hpp"

#include "Lib/System.hpp"
#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"

static unsigned getNumWorkers()
{
  CALL("ScheduleExecutor::getNumWorkers");

  unsigned cores = System::getNumberOfCores();
  cores = cores < 1 ? 1 : cores;
  unsigned workers = min(cores, env->options->multicore());
  if(!workers)
  {
    workers = cores >= 8 ? cores - 2 : cores;
  }
  return workers;
}

namespace CASC {
ScheduleExecutor::ScheduleExecutor(
  StrategyPriorityPolicy *policy,
  SliceExecutor *executor
) :
  _policy(policy),
  _executor(executor)
{
  CALL("ScheduleExecutor::ScheduleExecutor");
  _numWorkers = getNumWorkers();
}
} //namespace CASC
