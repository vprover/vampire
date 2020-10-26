

#ifndef __POLYNOMIAL_NORMALIZATION_H__
#define __POLYNOMIAL_NORMALIZATION_H__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/Theory.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {


class SimplifyingGeneratingLiteralSimplification
: public SimplifyingGeneratingInference1
{

protected:
  SimplifyingGeneratingLiteralSimplification(InferenceRule rule, Ordering& ordering);
  virtual Optional<LitEvalResult> simplifyLiteral(Literal* l) = 0;
  Result simplify(Clause* cl, bool doOrderingCheck) override;
private:
  Ordering* _ordering;
  const InferenceRule _rule;
};

class Cancellation
: public SimplifyingGeneratingLiteralSimplification
{
public:
  CLASS_NAME(Cancellation);
  USE_ALLOCATOR(Cancellation);

  Cancellation(Ordering& ordering);
  virtual ~Cancellation();

  Optional<LitEvalResult> simplifyLiteral(Literal*) override;
};


class PushUnaryMinus
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(PushUnaryMinus);
  USE_ALLOCATOR(PushUnaryMinus);

  virtual ~PushUnaryMinus();

  Clause* simplify(Clause* cl);
};


class PolynomialNormalization
: public SimplifyingGeneratingLiteralSimplification
{
public:
  CLASS_NAME(PolynomialNormalization);
  USE_ALLOCATOR(PolynomialNormalization);

  PolynomialNormalization(Ordering& ordering);
  virtual ~PolynomialNormalization();

protected:

  Optional<LitEvalResult> simplifyLiteral(Literal*) override;
  PolynomialNormalizer<PolynomialNormalizerConfig::Simplification<>> _normalizer;
};

};

#endif /* __POLYNOMIAL_NORMALIZATION_H__ */
