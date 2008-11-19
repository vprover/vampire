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
  TerminationReason terminationReason;
  Clause* refutation;
};

};

#endif /*__SaturationResult__*/
