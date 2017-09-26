/**
 * @file CASCMode.hpp
 * Defines class CASCMode.
 */

#ifndef __CASCMode__
#define __CASCMode__

#include "Forwards.hpp"

#include "Lib/Portability.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"

#include "Lib/VString.hpp"

#include "Shell/Property.hpp"

#include "Schedules.hpp"

namespace CASC
{

using namespace std;
using namespace Lib;
using namespace Shell;

class CASCMode {
public:
  CASCMode();
  virtual ~CASCMode() {}
  static bool perform(int argc,char* argv []);

  static unsigned getSliceTime(vstring sliceCode,vstring& chopped);

  /**
   * Run a slice corresponding to the options.
   * Return true iff the proof or satisfiability was found
   */
  bool runSlice(Options& opt);
  void childRun(Options& opt) NO_RETURN;

  void handleSIGINT() __attribute__((noreturn));

  /** The problem property, computed once in the parent process */
  Property* _property;

  typedef Set<vstring> StrategySet;
  bool perform();
  bool runSchedule(Schedule&,unsigned ds,StrategySet& remember,bool fallback);
  bool runSlice(vstring sliceCode, unsigned ds);

  ScopedPtr<Problem> _prb;



};

}

#endif // __CASCMode__
