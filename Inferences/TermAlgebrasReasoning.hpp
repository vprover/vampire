/**
 * @file TermAlgebrasReasoning.hpp
 *
 * Inference rules allowing efficient reasoning in the theory of term
 * algebras
 */

#ifndef __TermAlgebrasReasoning__
#define __TermAlgebrasReasoning__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

namespace Inferences {

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
  
};

#endif
