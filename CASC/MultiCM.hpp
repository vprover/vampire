/**
 * @file MultiCM.hpp
 * Defines class MultiCM.
 */

#ifndef __MultiCM__
#define __MultiCM__

#include "Forwards.hpp"

#include "Lib/ScopedPtr.hpp"
#include "Kernel/Problem.hpp"

#include "CASCMode.hpp"

namespace CASC
{

using namespace Lib;
using namespace Kernel;


class MultiCM
: public CASCMode 
{
public:
  MultiCM();

protected:
  bool runSchedule(Schedule&,unsigned ds,StrategySet& remember,bool fallback);
  bool runSlice(Options& opt){ ASSERTION_VIOLATION; };

private:
  void transformToOptionsList(Schedule& schedule);  
  ScopedPtr<Problem> _prb;
};

}

#endif // __MultiCM__
