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
 * @file MainLoop.hpp
 * Defines class MainLoop.
 */

#ifndef __MainLoop__
#define __MainLoop__

#include "Forwards.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"

#include "Shell/Statistics.hpp"

#include "Lib/Allocator.hpp"

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
  : terminationReason(reason), refutation(0), saturatedSet(0) {}
  MainLoopResult(TerminationReason reason, Clause* ref)
  : terminationReason(reason), refutation(ref), saturatedSet(0) {}

  void updateStatistics();

  TerminationReason terminationReason;
  Clause* refutation;
  UnitList* saturatedSet;
};



class MainLoop {
public:  
  CLASS_NAME(MainLoop);
  USE_ALLOCATOR(MainLoop);

  MainLoop(Problem& prb, const Options& opt) : _prb(prb), _opt(opt) {}
  virtual ~MainLoop() {}


  MainLoopResult run();
  static MainLoop* createFromOptions(Problem& prb, const Options& opt);

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

  /**
   * Return the problem that the solving algorithm is being run on
   */
  const Problem& getProblem() const { return _prb; }
  Problem& getProblem() { return _prb; }

  /**
   * Get options specifying strategy for the solving algorithm
   */
  const Options& getOptions() const { return _opt; }

  static bool isRefutation(Clause* cl);
protected:

  /**
   * This function is called after all initialization of the main loop
   * algorithm is done (especially when all the indexes are in place).
   *
   * In this function the implementing class should retrieve clauses
   * from the Problem object @c _prb and load them into the algorithm.
   *
   * In former versions the action taken by this method corresponded
   * to the function addInputClauses().
   */
  virtual void init() = 0;

  /**
   * The actual run of the solving algorithm should be implemented in
   * this function.
   */
  virtual MainLoopResult runImpl() = 0;

  Problem& _prb;

  /**
   * Options that represent the strategy used by the current main loop
   */
  const Options& _opt;
};

}

#endif // __MainLoop__
