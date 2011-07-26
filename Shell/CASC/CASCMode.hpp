/**
 * @file CASCMode.hpp
 * Defines class CASCMode.
 */

#ifndef __CASCMode__
#define __CASCMode__

#include <string>

#include "Forwards.hpp"

#include "Lib/Portability.hpp"
#include "Shell/Property.hpp"
#include "Lib/Set.hpp"

namespace Shell {
namespace CASC
{

using namespace std;

class CASCMode {
public:

  static bool perform(int argc,char* argv []);
protected:
  /**
   * Run a slice correponding to the options.
   * Return true iff the proof or satisfiability was found
   */
  virtual bool runSlice(Options& opt) = 0;

  void handleSIGINT() __attribute__((noreturn));
  /** The problem property, computed only once */
  Property* _property;

private:
  typedef Set<string> StrategySet;
  bool perform();
  bool runSchedule(const char** sliceCodes,unsigned ds,StrategySet& remember);
  bool runFallbackSchedule(const char** sliceCodes,unsigned ds,StrategySet& avoid);
  bool runSlice(string sliceCode, unsigned ds);
  unsigned getSliceTime(string sliceCode,string& chopped);
};

}
}

#endif // __CASCMode__
