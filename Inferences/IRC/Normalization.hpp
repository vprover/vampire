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
 * @file Normalization.hpp
 * Defines class Normalization
 *
 */

#ifndef __IRC_Normalization__
#define __IRC_Normalization__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Indexing/InequalityResolutionIndex.hpp"
#include "Kernel/IRC.hpp"

namespace Inferences {
namespace IRC {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Normalization
: public ImmediateSimplificationEngine 
{
  shared_ptr<IrcState> _shared;
public: 
  Normalization(shared_ptr<IrcState> shared) : _shared(std::move(shared)) {}
  CLASS_NAME(Normalization);
  USE_ALLOCATOR(Normalization);

  virtual Clause* simplify(Clause* cl) final override;
};

} // namespace IRC
} // namespace Inferences

#endif /*__IRC_Normalization__*/
