/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#if VTHREADED
#ifndef __ThreadScheduleExecutor__
#define __ThreadScheduleExecutor__

#include "ScheduleExecutor.hpp"

namespace CASC
{

class ThreadScheduleExecutor final : public ScheduleExecutor
{
public:
  CLASS_NAME(ThreadScheduleExecutor);
  USE_ALLOCATOR(ThreadScheduleExecutor);
  using ScheduleExecutor::ScheduleExecutor;
  bool run(const Schedule &schedule) override;
};
}

#endif
#endif
