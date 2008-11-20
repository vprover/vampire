/**
 * @file SaturationResult.hpp
 * Defines class SaturationResult
 *
 */

#ifndef __SaturationResult__
#define __SaturationResult__


namespace Saturation
{

struct SaturationResult
{
  enum TerminationReason {
    REFUTATION,
    SATISFIABLE,
    UNKNOWN,
    TIME_LIMIT,
    MEMORY_LIMIT
  };
  
  SaturationResult(TerminationReason reason)
  : terminationReason(reason) {}
  SaturationResult(TerminationReason reason, Clause* ref)
  : terminationReason(reason), refutation(ref) {}
  
  TerminationReason terminationReason;
  Clause* refutation;
};

};

#endif /*__SaturationResult__*/
