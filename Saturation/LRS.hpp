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

  /** Running cost of limit maintenance, against which the -lmb budget is checked.
   * Kept in both units because which one matters depends on which limit binds;
   * see bindingResourceIsInstructions(). */
  long long _maintenanceMicros = 0;   //< microseconds spent in updates
  long _maintenanceInstrs = 0;        //< mega-instructions spent in updates

  bool withinMaintenanceBudget();
  bool bindingResourceIsInstructions();

  /** Trace of limit-update decisions, for reproducing an LRS run exactly.
   * Opened lazily on first use from -lrs_save_trace_file / -lrs_load_trace_file.
   * Each record is "<pops accumulated when the update fired> <estimate returned>":
   * the decision has to be recorded as well as its result, because the cadence
   * consults the clock and so is not reproducible on its own. */
  std::unique_ptr<std::ofstream> _saveTrace;
  std::unique_ptr<std::ifstream> _loadTrace;
  bool _traceOpened = false;
  void openTraceFiles();

  /** Replay state: the next record read ahead from _loadTrace, and the result to
   * hand back for the update it describes. */
  bool _haveNextRecord = false;
  bool _traceExhausted = false;
  unsigned _nextRecordPops = 0;
  long long _nextRecordResult = -1;
  /** Pops that triggered the update currently being made, for _saveTrace. */
  unsigned _popsAtFire = 0;
  bool replaying() const { return _loadTrace != nullptr; }
  bool readNextRecord();
};

};

#endif /* __LRS__ */
