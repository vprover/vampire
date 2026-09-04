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
 * @file LRS.hpp
 * Defines class LRS.
 */


#ifndef __LRS__
#define __LRS__

#include "Forwards.hpp"

#include "Otter.hpp"

#include <fstream>
#include <memory>

namespace Saturation {

using namespace Kernel;

class LRS
: public Otter
{
public:
  using Otter::Otter;

protected:
  void afterUnprocessedLoop(unsigned popsElapsed) override;

  bool shouldUpdateLimits(unsigned popsElapsed);

  long long estimatedReachableCount();

private:
  /** Unprocessed pops seen since the last limit update. Carried across calls, so it
   * must be per-instance state: a function-local static would leak between Problems
   * solved in one process. */
  unsigned _leftoverPops = 0;

  /** Trace of limit-update decisions, for reproducing an LRS run exactly.
   * Opened lazily on first use from -lrs_save_trace_file / -lrs_load_trace_file. */
  std::unique_ptr<std::ofstream> _saveTrace;
  std::unique_ptr<std::ifstream> _loadTrace;
  bool _traceOpened = false;
  void openTraceFiles();
};

};

#endif /* __LRS__ */
