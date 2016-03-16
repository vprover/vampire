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
  
private:
  static bool distinctConstructorsEquality(Literal *lit);
};

class InjectivityGIE
  : public GeneratingInferenceEngine {
public:
  CLASS_NAME(InjectivityGIE);
  USE_ALLOCATOR(InjectivityGIE);
  
  Kernel::ClauseIterator generateClauses(Kernel::Clause* c);

private:
  static bool sameConstructorsPositiveEquality(Literal *lit);
  struct SubtermIterator;
  struct SubtermEqualityFn;
};

class AcyclicityGIE
  : public GeneratingInferenceEngine
{
public:
  CLASS_NAME(AcyclicityGIE);
  USE_ALLOCATOR(AcyclicityGIE);
  
  Kernel::ClauseIterator generateClauses(Kernel::Clause* c);
  
private:
  static List<TermList>* properSubterms(Kernel::TermList t, unsigned sort);
  static bool oneConstructorPositiveEquality(Literal *lit, TermList &fs, TermList &t);
  struct DeepSubtermIterator;
  struct SubtermInequalityFn;
};

  
};

#endif
