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
 * @file ForwardGroundReducibility.hpp
 * Defines class ForwardGroundReducibility
 *
 */

#ifndef __ForwardGroundReducibility__
#define __ForwardGroundReducibility__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

using Position = Stack<unsigned>;

class ForwardGroundReducibility
: public ForwardGroundSimplificationEngine
{
public:
  ForwardGroundReducibility(const Options& opts)
    : _redundancyCheck(opts.demodulationRedundancyCheck()!=Options::DemodulationRedundancyCheck::OFF),
      _encompassing(opts.demodulationRedundancyCheck()==Options::DemodulationRedundancyCheck::ENCOMPASS),
      _exhaustive(opts.conditionalRedundancySubsumption()) {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, ClauseIterator& replacements, ClauseIterator& premises) override;

#if VDEBUG
  void setTestIndices(const Stack<Index*>& indices) override {
    _index = static_cast<DemodulationLHSIndex*>(indices[0]);
  }
#endif // VDEBUG

private:
  const TermPartialOrdering* next(Stack<TermOrderingConstraint> ordCons);
  const TermPartialOrdering* skip();
  void pushNext();

  OrderingComparatorUP _comp;
  Stack<OrderingComparator::Branch*> _path;
  DemodulationLHSIndex* _index;
  bool _redundancyCheck;
  bool _encompassing;
  bool _exhaustive;
};

};

#endif /*__ForwardGroundReducibility__*/
