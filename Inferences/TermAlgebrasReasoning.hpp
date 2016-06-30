/**
 * @file TermAlgebrasReasoning.hpp
 *
 * Inference rules allowing efficient reasoning in the theory of term
 * algebras
 */

#ifndef __TermAlgebrasReasoning__
#define __TermAlgebrasReasoning__

#include "Forwards.hpp"

#include "Indexing/AcyclicityIndex.hpp"

#include "Inferences/InferenceEngine.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {

class DistinctnessGIE
  : public GeneratingInferenceEngine {
public:
  CLASS_NAME(DistinctnessGIE);
  USE_ALLOCATOR(DistinctnessGIE);
  
  Kernel::ClauseIterator generateClauses(Kernel::Clause* c);
  
private:
  struct ConstructorDisequalityIterator;
  struct ConstructorDisequalityFn;
};

class DistinctnessISE
  : public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(DistinctnessISE);
  USE_ALLOCATOR(DistinctnessISE);
  
  Kernel::Clause* simplify(Kernel::Clause* c);
};

class InjectivityGIE
  : public GeneratingInferenceEngine {
public:
  CLASS_NAME(InjectivityGIE);
  USE_ALLOCATOR(InjectivityGIE);
  
  Kernel::ClauseIterator generateClauses(Kernel::Clause* c);
  
private:
  struct ArgumentEqualityIterator;
  struct ArgumentEqualityFn;
};

class InjectivityGIE1
  : public GeneratingInferenceEngine {
public:
  CLASS_NAME(InjectivityGIE1);
  USE_ALLOCATOR(InjectivityGIE1);
  
  Kernel::ClauseIterator generateClauses(Kernel::Clause* c);

private:
  struct SubtermIterator;
  struct SubtermEqualityFn;
};

class InjectivityISE
  : public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(InjectivityISE);
  USE_ALLOCATOR(InjectivityISE);
  
  Kernel::Clause* simplify(Kernel::Clause* c);
};

class AcyclicityGIE
  : public GeneratingInferenceEngine {
public:
  CLASS_NAME(AcyclicityGIE);
  USE_ALLOCATOR(AcyclicityGIE);

  void attach(Saturation::SaturationAlgorithm* salg);
  void detach();
  Kernel::ClauseIterator generateClauses(Kernel::Clause *c);
private:
  struct AcyclicityGenIterator;
  struct AcyclicityGenFn;
  
  Indexing::AcyclicityIndex *_acyclIndex;
};
  
};

#endif
