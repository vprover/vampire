
/*
 * File InequalityResolution.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file InequalityResolution.hpp
 * Defines class InequalityResolution
 *
 */

#ifndef __InequalityResolution__
#define __InequalityResolution__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/InequalityNormalizer.hpp"

namespace Indexing {


class InequalityResolutionIndex
: public TermIndex
{
public:
  CLASS_NAME(InequalityResolutionIndex);
  USE_ALLOCATOR(InequalityResolutionIndex);

  InequalityResolutionIndex(TermIndexingStructure* is, Ordering& ord, InequalityNormalizer norm)
    : TermIndex(is)
    , _ord(&ord)
    , _normalizer(std::move(norm)) {}

  InequalityNormalizer const& normalizer() const { return _normalizer; }
  Ordering* ord() const { return _ord; }
protected:
  void handleClause(Clause* c, bool adding);
private:
  template<class NumTraits> bool handleLiteral(Literal* lit, Clause* c, bool adding);

  Ordering* _ord;
  InequalityNormalizer _normalizer;
};
}


namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class InequalityResolution
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InequalityResolution);
  USE_ALLOCATOR(InequalityResolution);

  InequalityResolution() 
    : _index(0)
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  ClauseIterator generateClauses(Clause* premise) final override;

  
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
private:

  template<class NumTraits> VirtualIterator<Monom<NumTraits>> maxTerms(InequalityLiteral<NumTraits> const& lit) const;
  template<class NumTraits> ClauseIterator generateClauses(Clause* clause, Literal* lit) const;

  InequalityNormalizer const& normalizer() const { return _index->normalizer(); }
  Ordering* ord() const { return _index->ord(); }
  InequalityResolutionIndex* _index;
};

};

#endif /*__InequalityResolution__*/
