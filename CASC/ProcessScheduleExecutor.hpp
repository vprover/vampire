/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __ProcessScheduleExecutor__
#define __ProcessScheduleExecutor__

#include "ScheduleExecutor.hpp"

namespace CASC
{

class ProcessScheduleExecutor final : public ScheduleExecutor
{
public:
  CLASS_NAME(ProcessScheduleExecutor);
  USE_ALLOCATOR(ProcessScheduleExecutor);
  using ScheduleExecutor::ScheduleExecutor;
  bool run(const Schedule &schedule) override;

private:
  pid_t spawn(Lib::vstring code, int remaminingTime);
};
}

#endif
