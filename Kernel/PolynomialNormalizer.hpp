
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Signature.hpp" 
#include "SortHelper.hpp"
#include "Sorts.hpp"
#include "TermIterators.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "num_traits.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/Either.hpp"
#include <algorithm>
#include <utility>


#ifndef __POLYNOMIAL_NORMALIZER_HPP__
#define __POLYNOMIAL_NORMALIZER_HPP__

namespace Kernel {


struct AnyPoly;
class TermEvalResult;
using LitEvalResult  = Lib::Coproduct<Literal*, bool>;

namespace PolynomialNormalizerConfig {
  struct Simplification { 
    constexpr static bool usePolyMul = true;
  };
  struct Normalization { 
    constexpr static bool usePolyMul = false;
  };
}

template<class Config>
class PolynomialNormalizer {
  // const bool _usePolyMul;
public:
  // PolynomialNormalizer(bool usePolyMul) : _usePolyMul(usePolyMul) {}
  LitEvalResult evaluate(Literal* in) const;
  TermList evaluate(TermList in) const;
  TermList evaluate(Term* in) const;

private:
  struct RecursionState;
  LitEvalResult evaluateStep(Literal* in) const;

  TermEvalResult evaluateStep(Term* orig, TermEvalResult* evaluatedArgs) const;
};

}

#include "PolynomialNormalizerImpl.hpp"

#endif // __POLYNOMIAL_NORMALIZER_HPP__
