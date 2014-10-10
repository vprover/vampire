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

namespace CASC
{

using namespace std;
using namespace Lib;
using namespace Shell;

class CASCMode {
public:
  virtual ~CASCMode() { }
  static bool perform(int argc,char* argv []);

  typedef Stack<string> Schedule;
  static void getSchedules(Property& prop, Schedule& quick, Schedule& fallback);
  static void getSchedulesSat(Property& prop, Schedule& quick, Schedule& fallback);
  static void getSchedulesEPR(Property& prop, Schedule& quick, Schedule& fallback);
  static unsigned getSliceTime(string sliceCode,string& chopped);
  static void makeSat() {_sat=true;}
  static void makeEPR() {_epr=true;}
  static void makeMulti() {_multi_strategy=true;}
protected:
  /**
   * Run a slice correponding to the options.
   * Return true iff the proof or satisfiability was found
   */
  virtual bool runSlice(Options& opt) = 0;

  /** 
   * We can override this if we have a different way of organising the
   * schedule i.e. in MultiCM
   */
  typedef Set<string> StrategySet;
  virtual bool runSchedule(Schedule&,unsigned ds,StrategySet& remember,bool fallback);

  void handleSIGINT() __attribute__((noreturn));

  /** The problem property, computed once in the parent process */
  Property* _property;
  /** True if satisfiability checking */
  static bool _sat;
  /** True if EPR formulas */
  static bool _epr;

  /** True if running in multi strategy mode **/
  static bool _multi_strategy;

private:
  bool perform();
  bool runSlice(string sliceCode, unsigned ds);

};

}

#endif // __CASCMode__
