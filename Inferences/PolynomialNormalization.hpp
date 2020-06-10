

#ifndef __POLYNOMIAL_NORMALIZATION_H__
#define __POLYNOMIAL_NORMALIZATION_H__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/Theory.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class PolynomialNormalization
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(PolynomialNormalization);
  USE_ALLOCATOR(PolynomialNormalization);

  PolynomialNormalization(Ordering& ordering) : _ordering(ordering) {}
  virtual ~PolynomialNormalization();

  Clause* simplify(Clause* cl);
private:

  PolynomialNormalizer<PolynomialNormalizerConfig::Simplification<>> _normalizer;
  Ordering& _ordering;
};

};

#endif /* __POLYNOMIAL_NORMALIZATION_H__ */
