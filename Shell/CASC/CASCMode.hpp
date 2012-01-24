/**
 * @file CASCMode.hpp
 * Defines class CASCMode.
 */

#ifndef __CASCMode__
#define __CASCMode__

#include <string>

#include "Forwards.hpp"

#include "Lib/Portability.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"

#include "Shell/Property.hpp"

namespace Shell {
namespace CASC
{

using namespace std;

class CASCMode {
public:
  virtual ~CASCMode() {}
  static bool perform(int argc,char* argv []);

  typedef Stack<string> Schedule;
  static void getSchedules(Property& prop, Schedule& quick, Schedule& fallback);
  static unsigned getSliceTime(string sliceCode,string& chopped);
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
  typedef Set<string> StrategySet;
  bool perform();
  bool runSchedule(Schedule&,unsigned ds,StrategySet& remember,bool fallback);
  bool runSlice(string sliceCode, unsigned ds);
};

}
}

#endif // __CASCMode__
