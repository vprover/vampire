
#ifndef __POLYNOMIAL_EVALUATION_H__
#define __POLYNOMIAL_EVALUATION_H__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/Polynomial.hpp"
#include "Kernel/Theory.hpp"

#include "InferenceEngine.hpp"

namespace Inferences 
{

class PolynomialEvaluation
: public SimplifyingGeneratingLiteralSimplification
{
public:
  CLASS_NAME(PolynomialEvaluation);
  USE_ALLOCATOR(PolynomialEvaluation);

  PolynomialEvaluation(Ordering& ordering);
  virtual ~PolynomialEvaluation();

private:

  Result simplifyLiteral(Literal*) override;

private:
  Option<PolyNf> evaluate(TermList in, unsigned sortNumber) const;
  Option<PolyNf> evaluate(Term* in) const;
  Option<PolyNf> evaluate(PolyNf in) const;
  Option<PolyNf> evaluate(TypedTermList in) const;

  Option<Result> evaluateStep(Literal* orig, PolyNf* evaluatedArgs) const;

  PolyNf evaluateStep(Term* orig, PolyNf* evaluatedArgs) const;
};


} // namespace Inferences 

#endif /* __POLYNOMIAL_EVALUATION_H__ */
