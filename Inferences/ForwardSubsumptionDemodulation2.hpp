#ifndef FORWARDSUBSUMPTIONDEMODULATION2_HPP
#define FORWARDSUBSUMPTIONDEMODULATION2_HPP

#include "InferenceEngine.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/RequestedIndex.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


/**
 * Forward Subsumption Demodulation (FSD) is a forward simplification rule
 * that combines subsumption and demodulation.
 *
 *      l = r \/ C        L[lΘ] \/ CΘ \/ D
 *     ------------------------------------
 *              L[rΘ] \/ CΘ \/ D
 *
 * where C, D are clauses and Θ is a substitution,
 * lΘ > rΘ   and   l = r  <  L[lΘ] \/ D.
 *
 * TODO:
 * Mention in this comment:
 * - Why do we need this?
 * - How does it help us? Maybe with a small example (a version that works with demodulation; then we introduce conditions s.t. we need FSD)
 * - Relation to conditional rewriting.
 */
class ForwardSubsumptionDemodulation2
  : public ForwardSimplificationEngine
{
  public:
    CLASS_NAME(ForwardSubsumptionDemodulation2);
    USE_ALLOCATOR(ForwardSubsumptionDemodulation2);

    ForwardSubsumptionDemodulation2(bool doSubsumption)
      : _doSubsumption(doSubsumption)
    { }

    void attach(SaturationAlgorithm* salg) override;
    void detach() override;
    bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

  private:
    RequestedIndex<LiteralIndex> _unitIndex;
    RequestedIndex<LiteralIndex> _index;

    bool _preorderedOnly;
    bool _allowIncompleteness;

    bool _doSubsumption;
};


}

#endif /* !FORWARDSUBSUMPTIONDEMODULATION2_HPP */
