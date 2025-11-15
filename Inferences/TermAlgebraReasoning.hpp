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
 * @file TermAlgebraReasoning.hpp
 *
 * Inference rules allowing efficient reasoning in the theory of term
 * algebras. These rules concerns (dis)equalities between terms of
 * sorts marked as term algebra sorts.
 */

#ifndef __TermAlgebraReasoning__
#define __TermAlgebraReasoning__

#include "Forwards.hpp"

#include "Indexing/AcyclicityIndex.hpp"

#include "Inferences/InferenceEngine.hpp"

#include "Kernel/Clause.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {

/*
  Simplification rule:

  f(...) = g(...) \/ A
  --------------------
          A

  Tautology deletion:

  f(...) ~= g(...) \/ A

  where f and g are different term algebra constructors
*/
class DistinctnessISE
  : public ImmediateSimplificationEngine
{

public:
  Kernel::Clause* simplify(Kernel::Clause* c) override;
};

/*
  Generating rule:

  f(s1 ... sn) = f(t1 ... tn) \/ A
  --------------------------------
            s1 = t1 \/ A
                ...
            sn = tn \/ A

  where f is a term algebra constructor of arity n > 1
*/
class InjectivityGIE
  : public GeneratingInferenceEngine {
public:
  Kernel::ClauseIterator generateClauses(Kernel::Clause* c) override;

private:
  struct SubtermIterator;
  struct SubtermEqualityFn;
};

/*
  Simplification rule:

  f(s) = f(t) \/ A
  ----------------
     s = t \/ A

  where f is a term algebra constructor of arity 1
*/
class InjectivityISE
  : public ImmediateSimplificationEngine
{
public:
  Kernel::Clause* simplify(Kernel::Clause* c) override;
};

class NegativeInjectivityISE
  : public ImmediateSimplificationEngine
{
public:
  Kernel::Clause* simplify(Kernel::Clause* c) override;

private:
  bool litCondition(Clause* c, unsigned i);
};

class AcyclicityGIE
  : public GeneratingInferenceEngine {
public:
  void attach(Saturation::SaturationAlgorithm* salg) override;
  void detach() override;
  Kernel::ClauseIterator generateClauses(Kernel::Clause *c) override;
private:
  struct AcyclicityGenIterator;
  struct AcyclicityGenFn;
  
  Indexing::AcyclicityIndex *_acyclIndex;
};

class AcyclicityGIE1
  : public GeneratingInferenceEngine {
public:
  Kernel::ClauseIterator generateClauses(Kernel::Clause* c) override;

private:
  struct SubtermDisequalityFn;
  struct LiteralIterator;
  struct SubtermDisequalityIterator;
};
  
};

#endif
