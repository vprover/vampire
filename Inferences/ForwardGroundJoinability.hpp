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
  virtual const char* name() const final override { return "ForwardGroundJoinability"; }

  static bool makeEqual(Literal* lit, Stack<TermOrderingConstraint>& res);

private:
  struct RedundancyCheck
  {
    RedundancyCheck(const Ordering& ord, Literal* data);
    std::pair<Literal*,const TermPartialOrdering*> next(Stack<TermOrderingConstraint> cons, Literal* data);

    void pushNext();

    using Branch = TermOrderingDiagram::Branch;
    using Tag = TermOrderingDiagram::Node::Tag;

    TermOrderingDiagramUP tod;
    TermOrderingDiagram::Traversal<TermOrderingDiagram::DefaultIterator> traversal;
    Branch* _curr;
  };

  DemodulationLHSIndex* _index;
};

};

#endif /*__ForwardGroundJoinability__*/
