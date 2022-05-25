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
 * @file ForwardDemodulation.hpp
 * Defines class ForwardDemodulation
 *
 */

#ifndef __ForwardDemodulation__
#define __ForwardDemodulation__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardDemodulation
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(ForwardDemodulation);
  USE_ALLOCATOR(ForwardDemodulation);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override = 0;
protected:
  bool _preorderedOnly;
  DemodulationLHSIndex* _index;
};

template <bool combinatorySupSupport>
class ForwardDemodulationImpl
: public ForwardDemodulation
{
public:
  CLASS_NAME(ForwardDemodulationImpl);
  USE_ALLOCATOR(ForwardDemodulationImpl);

  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
private:
};


};

#endif /*__ForwardDemodulation__*/
