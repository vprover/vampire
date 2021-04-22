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
 * @file InequalityFactoring.hpp
 * Defines class InequalityFactoring
 *
 */

#ifndef __InequalityFactoring__
#define __InequalityFactoring__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/InequalityNormalizer.hpp"
#include "Shell/Options.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class InequalityFactoring
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InequalityFactoring);
  USE_ALLOCATOR(InequalityFactoring);

  InequalityFactoring(InequalityFactoring&&) = default;
  InequalityFactoring(InequalityNormalizer normalizer, Ordering* ord, Shell::Options::UnificationWithAbstraction mode) 
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

};

#endif /*__InequalityFactoring__*/
