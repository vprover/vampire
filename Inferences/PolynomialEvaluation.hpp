/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __POLYNOMIAL_EVALUATION_H__
#define __POLYNOMIAL_EVALUATION_H__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/Polynomial.hpp"
#include "Kernel/Theory.hpp"

#include "InferenceEngine.hpp"


namespace Inferences 
{

using SortId = TermList;
class PolynomialEvaluation
: public SimplifyingGeneratingLiteralSimplification
{
public:
  PolynomialEvaluation(Ordering& ordering);
  virtual ~PolynomialEvaluation();

private:

  Result simplifyLiteral(Literal*) override;

  Lib::Option<PolyNf> evaluate(TermList in, SortId sortNumber) const;
  Lib::Option<PolyNf> evaluate(Term* in) const;
  Lib::Option<PolyNf> evaluate(PolyNf in) const;
  Lib::Option<PolyNf> evaluate(TypedTermList in) const;

  Lib::Option<Result> tryEvalPredicate(Literal* orig, PolyNf* evaluatedArgs) const;

  PolyNf evaluateStep(Term* orig, PolyNf* evaluatedArgs) const;
};


} // namespace Inferences 

#endif /* __POLYNOMIAL_EVALUATION_H__ */
