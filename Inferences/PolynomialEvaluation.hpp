
#ifndef __POLYNOMIAL_EVALUATION_H__
#define __POLYNOMIAL_EVALUATION_H__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/Theory.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {
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
  PolynomialNormalizer _normalizer;
};

};

#endif /* __POLYNOMIAL_EVALUATION_H__ */
