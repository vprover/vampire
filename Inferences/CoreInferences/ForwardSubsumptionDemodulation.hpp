/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

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
 * Subsumption Demodulation is a simplification rule that generalizes
 * demodulation by combining subsumption and demodulation.
 * The rule is defined as follows:
 *
 *      l = r \/ C        L[lΘ] \/ CΘ \/ D
 *     ------------------------------------
 *              L[rΘ] \/ CΘ \/ D
 *
 * where
 * - C, D are clauses and Θ is a substitution,
 * - lΘ > rΘ, and
 * - L[lΘ] \/ D > (l = r)Θ.
 *
 * For a detailed description, see the paper
 *
 *    Bernhard Gleiss, Laura Kovács, Jakob Rath:
 *    Subsumption Demodulation in First-Order Theorem Proving.
 *    Accepted for IJCAR 2020.
 *
 * This class implements the forward direction.
 */
class ForwardSubsumptionDemodulation
  : public ForwardSimplificationEngine
{
  public:
    CLASS_NAME(ForwardSubsumptionDemodulation);
    USE_ALLOCATOR(ForwardSubsumptionDemodulation);

    ForwardSubsumptionDemodulation(bool doSubsumption)
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

#endif /* !FORWARDSUBSUMPTIONDEMODULATION_HPP */
