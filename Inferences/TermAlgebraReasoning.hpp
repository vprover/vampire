
/*
 * File TermAlgebraReasoning.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
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

#include "Indexing/TermAlgebraIndex.hpp"

#include "Inferences/InferenceEngine.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

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
  CLASS_NAME(DistinctnessISE);
  USE_ALLOCATOR(DistinctnessISE);
  
  Kernel::Clause* simplify(Kernel::Clause* c);
};

/*
  Generating rule:

      f(...) = x \/ A
  -----------------------
  A { x <- g(y1 ... yn) }

  for constructor g s.t. f != g

  yi's fresh variables
 */
class Distinctness1GIE
  : public GeneratingInferenceEngine {
public:
  CLASS_NAME(Distinctness1GIE);
  USE_ALLOCATOR(Distinctness1GIE);

  Kernel::ClauseIterator generateClauses(Kernel::Clause* c);

private:
  struct Distinctness1GenFn;
  struct Distinctness1GenIterator; 
};

/*
  This class implements two generating rules at once:

  Distinctness rule:

  f(...) = u \/ A      g(...) = u' \/ B
  -------------------------------------
             (A \/ B)\sigma

  where sigma = mgu(u, u')
        f(...)\sigma not smaller than u\sigma
        g(...)\sigma not smaller than u'\sigma

  Injectivity rule:

  f(s1 ... sn) = u \/ A      f(t1 ... tn) = u' \/ B
  -------------------------------------------------
             (si = ti \/ A \/ B)\sigma

  where sigma = mgu(u, u')
        f(...)\sigma not smaller than u\sigma
        f(...)\sigma not smaller than u'\sigma

 */
class DistAndInj2GIE
  : public GeneratingInferenceEngine {
public:
  CLASS_NAME(DistAndInj2GIE);
  USE_ALLOCATOR(DistAndInj2GIE);

  void attach(SaturationAlgorithm* salg);
  void detach();

  Kernel::ClauseIterator generateClauses(Kernel::Clause* c);

private:
  struct DistAndInj2PerformFn;
  struct DistAndInj2GenFn;
  struct Injectivity2Iterator;

  static Clause* distinctnessConclusion(Clause *c1, Clause *c2, Literal *lit1, Literal *lit2, ResultSubstitutionSP sigma);

  Indexing::TARulesRHSIndex *_index;
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
  CLASS_NAME(InjectivityGIE);
  USE_ALLOCATOR(InjectivityGIE);
  
  Kernel::ClauseIterator generateClauses(Kernel::Clause* c);

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
  CLASS_NAME(InjectivityISE);
  USE_ALLOCATOR(InjectivityISE);
  
  Kernel::Clause* simplify(Kernel::Clause* c);
};

/*
  Generating rule:

  f(s1 ... sn) = x \/ A
  ---------------------
   si = yi \/ A\sigma

  where sigma = { x <- f(y1 ... yn) }

  yi's fresh variables
 */
class Injectivity1GIE
  : public GeneratingInferenceEngine {
public:
  CLASS_NAME(Injectivity1GIE);
  USE_ALLOCATOR(Injectivity1GIE);

  Kernel::ClauseIterator generateClauses(Kernel::Clause* c);

private:
  struct Injectivity1GenIterator;
  struct Injectivity1GenFn;
};

/*
  Simplification rule:

  f(s1 ... sn) != f(t1 ... tn) \/ A
  ---------------------------------
  s1 != t1 \/ ... \/ t1 != tn \/ A

  The soundness of the rule is not a property of injectivity but only
  of f being a function.
  
  However since f is injective the conclusion is equivalent to the
  premise and can be removed (not true of arbitrary functions)
 */
class NegativeInjectivityISE
  : public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(NegativeInjectivityISE);
  USE_ALLOCATOR(NegativeInjectivityISE);

  Kernel::Clause* simplify(Kernel::Clause* c);

private:
  bool litCondition(Clause* c, unsigned i);
};

/*
  The hyper-resolution rule presented in the Vampire workshop paper
 */
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
  
  Indexing::ChainIndex *_chainIndex;
};

class UniquenessGIE
  : public GeneratingInferenceEngine {
public:
  CLASS_NAME(UniquenessGIE);
  USE_ALLOCATOR(UniquenessGIE);

  void attach(Saturation::SaturationAlgorithm* salg);
  void detach();
  Kernel::ClauseIterator generateClauses(Kernel::Clause *c);
private:
  struct UniquenessGenIterator;
  struct UniquenessGenFn;
  
  Indexing::ChainIndex *_chainIndex;
};

/*
  Simplification rule
  
  x = t1 \/ ... \/ x = t2 \/ A
  ----------------------------
               A

  if the type of x is a (co)datatype with infinite domain and x does
  not occur in t1, ..., t2 or A
 */
class InfinitenessISE
  : public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(InfinitenessISE);
  USE_ALLOCATOR(InfinitenessISE);

  Kernel::Clause* simplify(Kernel::Clause* c);

private:
  Kernel::Clause* deleteLits(Kernel::Clause* c, TermList var, bool* positions);
};
  
};

#endif
