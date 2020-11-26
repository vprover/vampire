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
 * @file ForwardLiteralRewriting.hpp
 * Defines class ForwardLiteralRewriting.
 */


#ifndef __ForwardLiteralRewriting__
#define __ForwardLiteralRewriting__

#include "Forwards.hpp"
#include "Indexing/LiteralIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardLiteralRewriting
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(ForwardLiteralRewriting);
  USE_ALLOCATOR(ForwardLiteralRewriting);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;
private:
  RewriteRuleIndex* _index;
};

};

#endif /* __ForwardLiteralRewriting__ */
