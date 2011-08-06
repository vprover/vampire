/**
 * @file MainLoop.hpp
 * Defines class MainLoop.
 */

#ifndef __MainLoop__
#define __MainLoop__

#include "Forwards.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"

#include "Shell/Statistics.hpp"

namespace Shell {
  class Property;
};

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

  MainLoopResult run();
  static MainLoopSP createFromOptions(Shell::Property* prop);

  /**
   * A struct that is thrown as an exception when a refutation is found
   * during the main loop.
   */
  struct RefutationFoundException : public ThrowableBase
  {
    RefutationFoundException(Clause* ref) : refutation(ref)
    {
      CALL("MainLoop::RefutationFoundException::RefutationFoundException");
      ASS(isRefutation(ref));
    }

    Clause* refutation;
  };

  /**
   * A struct that is thrown as an exception when a refutation is found
   * during the main loop.
   */
  struct MainLoopFinishedException : public ThrowableBase
  {
    MainLoopFinishedException(const MainLoopResult& res) : result(res)
    {
    }

    MainLoopResult result;
  };

protected:
  virtual MainLoopResult runImpl() = 0;

  static bool isRefutation(Clause* cl);
  static ImmediateSimplificationEngineSP createISE();
};

}

#endif // __MainLoop__
