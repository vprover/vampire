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

#include <optional>
#include <filesystem>

#include "Forwards.hpp"

#include "Lib/ScopedPtr.hpp"

#include "Kernel/Problem.hpp"

#include "Shell/Property.hpp"
#include "Schedules.hpp"

namespace CASC
{

using namespace Lib;
using namespace Shell;

class PortfolioMode {
  PortfolioMode(Kernel::Problem* problem);
public:
  static bool perform(Kernel::Problem* problem);

  static void rescaleScheduleLimits(const Schedule& sOld, Schedule& sNew, float limit_multiplier);
  static void addScheduleExtra(const Schedule& sOld, Schedule& sNew, std::string extra);

private:
  // some of these names are kind of arbitrary and should be perhaps changed
  unsigned getSliceTime(const std::string &sliceCode);
  bool searchForProof();
  bool prepareScheduleAndPerform(const Shell::Property& prop);
  void getSchedules(const Property& prop, Schedule& quick, Schedule& champions);

  // returns a path to a temporary file with a proof in it on success
  std::optional<std::filesystem::path> runSchedule(Schedule schedule);
  bool runScheduleAndRecoverProof(Schedule schedule);
  [[noreturn]] void runSlice(std::string sliceCode, int remainingTime, bool scheduleRepeat);
  [[noreturn]] void runSlice(Options& strategyOpt);

  unsigned _numWorkers;

  /**
   * Problem that is being solved.
   *
   * Note that in the current process this child object is the only one that
   * will be using the problem object.
   */
  ScopedPtr<Problem> _prb;
  float _slowness;
};

}

#endif // __PortfolioMode__
