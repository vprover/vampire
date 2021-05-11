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
 * @file LiteralFactoring.hpp
 * Defines class LiteralFactoring
 *
 */

#ifndef __LiteralFactoring__
#define __LiteralFactoring__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Indexing/InequalityResolutionIndex.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace InequalityResolutionCalculus {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class LiteralFactoring
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(LiteralFactoring);
  USE_ALLOCATOR(LiteralFactoring);

  LiteralFactoring(LiteralFactoring&&) = default;
  LiteralFactoring(InequalityNormalizer normalizer, Ordering* ord, Shell::Options::UnificationWithAbstraction mode) 
    : _normalizer(normalizer)
    , _ord(ord)
    , _mode(mode)
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  ClauseIterator generateClauses(Clause* premise) final override;

  

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif

private:

  template<class NumTraits> ClauseIterator generateClauses(Clause* clause, Literal* lit) const;

  InequalityNormalizer const& normalizer() const { return _normalizer; }
  Ordering* ord() const { return _ord; }
  
  InequalityNormalizer _normalizer;
  Ordering* _ord;
  Shell::Options::UnificationWithAbstraction const _mode;
};

} // namespace InequalityResolutionCalculus 
} // namespace Inferences 

#endif /*__LiteralFactoring__*/
