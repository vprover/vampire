/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __BackwardSubsumptionDemodulation__
#define __BackwardSubsumptionDemodulation__

#include "InferenceEngine.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/RequestedIndex.hpp"
#include "Kernel/MLMatcherSD.hpp"

namespace Inferences {

using namespace Indexing;
using namespace Kernel;


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
 * This class implements the backward direction.
 */
class BackwardSubsumptionDemodulation
  : public BackwardSimplificationEngine
{
  public:
    CLASS_NAME(BackwardSubsumptionDemodulation);
    USE_ALLOCATOR(BackwardSubsumptionDemodulation);

    BackwardSubsumptionDemodulation();

    void attach(SaturationAlgorithm* salg) override;
    void detach() override;

    void perform(Clause* premise, BwSimplificationRecordIterator& simplifications) override;

  private:
    RequestedIndex<SimplifyingLiteralIndex> _index;

    bool _preorderedOnly;
    bool _allowIncompleteness;

    void performWithQueryLit(Clause* premise, Literal* candidateQueryLit, vvector<BwSimplificationRecord>& simplifications);
    bool simplifyCandidate(Clause* sideCl, Clause* mainCl, vvector<BwSimplificationRecord>& simplifications);
    bool rewriteCandidate(Clause* sideCl, Clause* mainCl, MLMatcherSD const& matcher, Clause*& replacement);
};

};

#endif /* __BackwardSubsumptionDemodulation__ */
