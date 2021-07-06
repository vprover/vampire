#include "FwdDemodulationModuloLA.hpp"


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
 * Perform forward simplification on @b cl
 *
 * Return true if the simplification is applicable on @b cl,
 * set @b replacement to a replacing clause if there is one (otherwise keep @b replacement = nullptr)
 *
 * @b premises will contain clauses that justify the simplification
 * performed.
 */
bool FwdDemodulationModLA::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override 
{
  UNIMPLEMENTED
}

} // namespace IRC
} // namespace Inferences
