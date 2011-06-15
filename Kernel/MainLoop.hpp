/**
 * @file MainLoop.hpp
 * Defines class MainLoop.
 */

#ifndef __MainLoop__
#define __MainLoop__

#include "Forwards.hpp"

#include "Lib/Environment.hpp"

#include "Shell/Statistics.hpp"

namespace Kernel {

using namespace Lib;
using namespace Inferences;
using namespace Shell;

struct MainLoopResult
{
  typedef Statistics::TerminationReason TerminationReason;

  MainLoopResult(TerminationReason reason)
  : terminationReason(reason) {}
  MainLoopResult(TerminationReason reason, Clause* ref)
  : terminationReason(reason), refutation(ref) {}

  void updateStatistics();

  TerminationReason terminationReason;
  Clause* refutation;
};


class MainLoop {
public:
  virtual ~MainLoop() {}
  virtual void addInputClauses(ClauseIterator cit) = 0;
  virtual MainLoopResult run() = 0;

  static MainLoopSP createFromOptions();

protected:
  static bool isRefutation(Clause* cl);
  static ImmediateSimplificationEngineSP createISE();
};

}

#endif // __MainLoop__
