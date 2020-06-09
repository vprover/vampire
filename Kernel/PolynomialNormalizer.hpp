
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Signature.hpp" 
#include "SortHelper.hpp"
#include "Sorts.hpp"
#include "TermIterators.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "NumTraits.hpp"
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

  template<class Ord = std::less<TermList>>
  struct Simplification { 
    using Ordering = Ord;
    constexpr static bool usePolyMul = false;
  };

  template<class Ord = std::less<TermList>>
  struct Normalization { 
    using Ordering = Ord;
    constexpr static bool usePolyMul = true;
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
