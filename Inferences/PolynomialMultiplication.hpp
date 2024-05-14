/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __Inference_PolynomialMultiplication__
#define __Inference_PolynomialMultiplication__

#include "InferenceEngine.hpp"
#include "Lib/Set.hpp"
#include "Kernel/Clause.hpp"
#include "LfpRule.hpp"
#include "Kernel/Polynomial.hpp"
#include "Kernel/KBO.hpp"

namespace Inferences {

class PolynomialMultiplication 
  : public SimplifyingGeneratingLiteralSimplification 
{
public:
  // CHECK OUT: 
  // Vampire uses its on allocator. We need to add these two marcro 
  // calls to every class that will be heap allocated at some point.
  USE_ALLOCATOR(PolynomialMultiplication);

  PolynomialMultiplication(Ordering& ord) : SimplifyingGeneratingLiteralSimplification(InferenceRule::POLYNOMIAL_MULTIPLICATION, ord) {}


#if VDEBUG
  // TODO this is a bit of a hack that needs to be resolved by me (joe) before merging. it is only needed for unit testing and is actually resolved on a not yet merged branch. Pls remind me to do this before merging! Cheers
  PolynomialMultiplication() : SimplifyingGeneratingLiteralSimplification(InferenceRule::POLYNOMIAL_MULTIPLICATION, *new KBO(KBO::testKBO())) {}
#endif

  SimplifyingGeneratingLiteralSimplification::Result simplifyLiteral(Literal* l) override;

private:
  Kernel::PolyNf evaluateStep(Kernel::PolyNf origTerm, Kernel::PolyNf* evalutedArgs);

  struct Evaluator {
    PolynomialMultiplication& self;
    using Arg    = Kernel::PolyNf;
    using Result = Kernel::PolyNf;
    Result operator()(Arg const& orig, Result* evalutedChildren)
    { return self.evaluateStep(orig, evalutedChildren); }
  };

};

} // namespace Inferences

#endif // __Inference_PolynomialMultiplication__
