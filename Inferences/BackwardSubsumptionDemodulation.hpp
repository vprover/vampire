/*
 * File BackwardSubsumptionDemodulation.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions.
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide.
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

    void perform2(Clause* premise, Literal* candidateQueryLit, v_vector<BwSimplificationRecord>& simplifications);
    bool simplifyCandidate(Clause* sideCl, Clause* mainCl, v_vector<BwSimplificationRecord>& simplifications);
    bool simplifyCandidate2(Clause* sideCl, Clause* mainCl, MLMatcherSD const& matcher, Clause*& replacement);
};

};

#endif /* __BackwardSubsumptionDemodulation__ */
