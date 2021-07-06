#include "BwdDemodulationModLA.hpp"


namespace Inferences {
namespace IRC {

////////////////////////////////////////////////////////////////////////////////////////////////////
// INDEXING
////////////////////////////////////////////////////////////////////////////////////////////////////

void BwdDemodulationModLA::attach(SaturationAlgorithm* salg)
{
  UNIMPLEMENTED
}

void BwdDemodulationModLA::detach()
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
void BwdDemodulationModLA::perform(Clause* premise, BwSimplificationRecordIterator& simplifications)
{
  UNIMPLEMENTED
}

} // namespace IRC
} // namespace Inferences
