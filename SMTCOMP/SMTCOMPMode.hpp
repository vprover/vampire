/**
 * @file SMTCOMPMode.hpp
 * Defines class SMTCOMPMode.
 */

#ifndef __SMTCOMPMode__
#define __SMTCOMPMode__

#include "Forwards.hpp"

#include "Lib/Portability.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"

#include "Lib/VString.hpp"

#include "Shell/Property.hpp"

namespace SMTCOMP 
{

using namespace std;
using namespace Lib;
using namespace Shell;

class SMTCOMPMode {
public:
  virtual ~SMTCOMPMode() {}
  static bool perform(int argc,char* argv []);

  typedef Stack<vstring> Schedule;
  static void getSchedules(Property& prop, Schedule& quick, Schedule& fallback);
  static unsigned getSliceTime(vstring sliceCode,vstring& chopped);
protected:
  /**
   * Run a slice correponding to the options.
   * Return true iff the proof or satisfiability was found
   */
  virtual bool runSlice(Options& opt) = 0;

  void handleSIGINT() __attribute__((noreturn));

  /** The problem property, computed once in the parent process */
  Property* _property;

private:
  typedef Set<vstring> StrategySet;
  bool perform();
  bool runSchedule(Schedule&,unsigned ds,StrategySet& remember,bool fallback);
  bool runSlice(vstring sliceCode, unsigned ds);
};

}

#endif // __SMTCOMPMode__
