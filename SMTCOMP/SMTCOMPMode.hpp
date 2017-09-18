/**
 * @file SMTCOMPMode.hpp
 * Defines class SMTCOMPMode.
 */

#ifndef __SMTCOMPMode__
#define __SMTCOMPMode__

#include <utility>

#include "Forwards.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Portability.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "Lib/VString.hpp"

#include "Lib/Sys/Semaphore.hpp"

#include "Kernel/Problem.hpp"

#include "Shell/Property.hpp"
#include "Shell/SineUtils.hpp"

namespace SMTCOMP {

using namespace std;
using namespace Lib;
using namespace Kernel;


class SMTCOMPMode
{
  enum {
    SEM_LOCK = 0,
    SEM_PRINTED = 1
  };

public:
  SMTCOMPMode() : _syncSemaphore(2)
{
  // We need the following two values because the way the semaphore class is currently implemented:
  // 1) dec is the only operation which is blocking
  // 2) dec is done in the mode SEM_UNDO, so is undone when a process terminates

  _syncSemaphore.set(SEM_LOCK,1);    // to synchronize access to the second field
  _syncSemaphore.set(SEM_PRINTED,0); // to indicate that a child has already printed result (it should only happen once)
}

  static bool perform();
private:
  static ostream& lineOutput();
  static ostream& coutLineOutput();

  typedef Set<vstring> StrategySet;
  typedef Stack<vstring> Schedule;
  static void getSchedules(Property& prop, Schedule& quick, Schedule& fallback);

  bool searchForProof();

  bool runSchedule(Schedule&,StrategySet& remember,bool fallback,int terminationTime);
  unsigned getSliceTime(vstring sliceCode,vstring& chopped);

  bool performStrategy(Shell::Property* property);
  bool waitForChildAndCheckIfProofFound();

  void runSlice(vstring slice, unsigned milliseconds) __attribute__((noreturn));
  void runSlice(Options& strategyOpt) __attribute__((noreturn));

#if VDEBUG
  DHSet<pid_t> childIds;
#endif

  /**
   * Problem that is being solved.
   *
   * Note that in the current process this child object is the only one that
   * will be using the problem object.
   */
  ScopedPtr<Problem> prb;

  Semaphore _syncSemaphore; // semaphore for synchronizing proof printing
};

}

#endif // __SMTCOMPMode__
