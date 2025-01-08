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
 * @file RenamingSuperposition.hpp
 * Defines class RenamingSuperposition
 *
 */

#ifndef __RenamingSuperposition__
#define __RenamingSuperposition__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

using Position = Stack<unsigned>;

class RenamingSuperposition
: public GeneratingInferenceEngine
{
public:
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  ClauseIterator generateClauses(Clause* cl) override;

#if VDEBUG
  void setTestIndices(const Stack<Index*>& indices) override {
    _index = static_cast<DemodulationLHSIndex*>(indices[0]);
  }
#endif // VDEBUG

private:
  DemodulationLHSIndex* _index;
};

};

#endif /*__RenamingSuperposition__*/
