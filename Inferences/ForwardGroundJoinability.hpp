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
: public ForwardGroundSimplificationEngine
{
public:
  ForwardGroundJoinability(const Options& opts)
    : _redundancyCheck(opts.demodulationRedundancyCheck()!=Options::DemodulationRedundancyCheck::OFF),
      _encompassing(opts.demodulationRedundancyCheck()==Options::DemodulationRedundancyCheck::ENCOMPASS) {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, ClauseIterator& premises) override;

#if VDEBUG
  void setTestIndices(const Stack<Index*>& indices) override {
    _index = static_cast<DemodulationLHSIndex*>(indices[0]);
  }
#endif // VDEBUG

  static bool makeEqual(TermList lhs, TermList rhs, Stack<TermOrderingConstraint>& res);

private:
  struct State {
    TermList left;
    TermList right;
    bool L;
    bool R;
  };

  friend std::ostream& operator<<(std::ostream& str, const State& s)
  { return str << s.left << (s.L ? "!" : "") << " ↓ " << s.right << (s.R ? "!" : ""); }

  struct RedundancyCheck {
    RedundancyCheck(const Ordering& ord, State* data);
    std::pair<State*,const TermPartialOrdering*> next(Stack<TermOrderingConstraint> cons, State* data);

    void pushNext();

    using Branch = OrderingComparator::Branch;
    using Tag = OrderingComparator::Node::Tag;

    OrderingComparatorUP comp;
    Stack<OrderingComparator::Branch*> path;
  };

  std::pair<State*,const TermPartialOrdering*> getNext(
    RedundancyCheck& checker, State* curr, Stack<TermOrderingConstraint> cons, TermList left, TermList right);

  DemodulationLHSIndex* _index;
  Stack<State*> _states;
  bool _redundancyCheck;
  bool _encompassing;
};

};

#endif /*__ForwardGroundJoinability__*/
