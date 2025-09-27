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

#include "DemodulationHelper.hpp"
#include "InferenceEngine.hpp"
#include "ProofExtra.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardDemodulation
: public ForwardSimplificationEngine
{
public:
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
protected:
  bool _preorderedOnly;
  bool _encompassing;
  bool _useTermOrderingDiagrams;
  bool _skipNonequationalLiterals;
  DemodulationHelper _helper;
  DemodulationLHSIndex* _index;
};

using ForwardDemodulationExtra = RewriteInferenceExtra;

};

#endif /*__ForwardDemodulation__*/
