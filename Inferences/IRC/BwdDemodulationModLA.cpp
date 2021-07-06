#include "BwdDemodulationModuloLA.hpp"


namespace Inferences {
namespace IRC {

////////////////////////////////////////////////////////////////////////////////////////////////////
// INDEXING
////////////////////////////////////////////////////////////////////////////////////////////////////

void attach(SaturationAlgorithm* salg) final override
{
  UNIMPLEMENTED
}

void detach() final override
{
  UNIMPLEMENTED
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// RULE APPLICATION
////////////////////////////////////////////////////////////////////////////////////////////////////


/**
 * Perform backward simplification with @b premise.
 *
 * Descendant classes should pay attention to the possibility that
 * the premise could be present in the simplification indexes at
 * the time of call to this method.
 */
bool BwdDemodulationModLA::perform(Clause* premise, BwSimplificationRecordIterator& simplifications) override 
{
  UNIMPLEMENTED
}

} // namespace IRC
} // namespace Inferences
