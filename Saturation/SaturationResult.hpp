/**
 * @file SaturationResult.hpp
 * Defines class SaturationResult
 *
 */

#ifndef __SaturationResult__
#define __SaturationResult__

#include "../Forwards.hpp"
#include "../Shell/Statistics.hpp"
#include "../Lib/Environment.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;

struct SaturationResult
{
  typedef Statistics::TerminationReason TerminationReason;
  
  SaturationResult(TerminationReason reason)
  : terminationReason(reason) {}
  SaturationResult(TerminationReason reason, Clause* ref)
  : terminationReason(reason), refutation(ref) {}

  void updateStatistics();
  
  TerminationReason terminationReason;
  Clause* refutation;
};

};

#endif /*__SaturationResult__*/
