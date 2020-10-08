

#ifndef __POLYNOMIAL_NORMALIZATION_H__
#define __POLYNOMIAL_NORMALIZATION_H__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/Theory.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class MaybeImmediateSimplification
: public ImmediateSimplificationEngine
, public SimplifyingGeneratingInference
{
public:
  Clause* simplify(Clause* cl) override;
  ClauseGenerationResult generateClauses(Clause* cl) override;

  
protected:
  virtual pair<Clause*, bool> simplify(Clause* cl, bool doOrderingCheck) = 0;
};


class MaybeImmediateLiteralSimplification
: public MaybeImmediateSimplification
{

protected:
  MaybeImmediateLiteralSimplification(InferenceRule rule, Ordering& ordering);
  virtual Optional<LitEvalResult> simplifyLiteral(Literal* l) = 0;
  pair<Clause*, bool> simplify(Clause* cl, bool doOrderingCheck) override;
private:
  Ordering* _ordering;
  const InferenceRule _rule;
};

class Cancellation
: public MaybeImmediateLiteralSimplification
{
public:
  CLASS_NAME(Cancellation);
  USE_ALLOCATOR(Cancellation);

  Cancellation(Ordering& ordering);
  virtual ~Cancellation();

  Optional<LitEvalResult> simplifyLiteral(Literal*) override;
  // Clause* simplify(Clause* cl);
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
: public MaybeImmediateLiteralSimplification
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
