#ifndef FORWARDSUBSUMPTIONDEMODULATION_HPP
#define FORWARDSUBSUMPTIONDEMODULATION_HPP

#include "InferenceEngine.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/RequestedIndex.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


/**
 * Combines subsumption and demodulation into a forward simplifying rule.
 *
 * Simplified version without substitutions for clauses C, D:
 *
 *      s = t \/ C   L[s] \/ C \/ D
 *      ---------------------------
 *            C \/ D[t]
 *
 *
 *
 *      l = r \/ C        L[lΘ] \/ CΘ \/ D
 *      ----------------------------------
 *              L[rΘ] \/ CΘ \/ D
 *
 *
 *
 */
class ForwardSubsumptionDemodulation
  : public ForwardSimplificationEngine
{
  public:
    CLASS_NAME(ForwardSubsumptionDemodulation);
    USE_ALLOCATOR(ForwardSubsumptionDemodulation);

    void attach(SaturationAlgorithm* salg) override;
    void detach() override;
    bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

  private:
    RequestedIndex<LiteralIndex> _index;

    bool _preorderedOnly;
    bool _performRedundancyCheck;
};


}

#endif /* !FORWARDSUBSUMPTIONDEMODULATION_HPP */
