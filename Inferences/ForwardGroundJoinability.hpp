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

#include "DemodulationHelper.hpp"
#include "InferenceEngine.hpp"
#include "ProofExtra.hpp"

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
protected:
  DemodulationHelper _helper;
  DemodulationLHSIndex* _index;
};

using ForwardDemodulationExtra = RewriteInferenceExtra;

};

#endif /*__ForwardDemodulation__*/
