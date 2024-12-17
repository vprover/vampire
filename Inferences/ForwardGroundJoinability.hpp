/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file ForwardGroundJoinability.hpp
 * Defines class ForwardGroundJoinability
 *
 */

#ifndef __ForwardGroundJoinability__
#define __ForwardGroundJoinability__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardGroundJoinability
: public ForwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

#if VDEBUG
  void setTestIndices(const Stack<Index*>& indices) override {
    _index = static_cast<DemodulationLHSIndex*>(indices[0]);
  }
#endif // VDEBUG

protected:
  TermList normalize(TermList t, const TermPartialOrdering* tpo) const;

  DemodulationLHSIndex* _index;

  struct RedundancyCheck {
    RedundancyCheck(const Ordering& ord, void* data);
    std::pair<void*,const TermPartialOrdering*> next(OrderingConstraints cons, void* data);

    void pushNext();

    using Branch = OrderingComparator::Branch;
    using BranchTag = OrderingComparator::BranchTag;

    OrderingComparatorUP comp;
    Stack<OrderingComparator::Branch*> path;
  };
};

};

#endif /*__ForwardDemodulation__*/
