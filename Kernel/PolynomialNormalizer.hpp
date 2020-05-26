
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
//  TODO continue here
using TermEvalResult = Lib::Either<TermList, AnyPoly>;
using LitEvalResult  = Lib::Either<Literal*, bool>;
struct PolynomialNormalizer {

public:
  LitEvalResult evaluate(Literal* in) const;
  TermList evaluate(TermList in) const;
  TermList evaluate(Term* in) const;

private:
  struct RecursionState;
  LitEvalResult evaluateStep(Literal* in) const;

  TermEvalResult evaluateStep(Term* orig, TermEvalResult* evaluatedArgs) const;

  template<Theory::Interpretation inter>
  LitEvalResult evaluateLit(Literal* lit) const;

  template<Theory::Interpretation inter>
  TermEvalResult evaluateFun(Term* orig, TermEvalResult* evaluatedArgs) const;

  template<class CommutativeMonoid>
  TermEvalResult evaluateCommutativeMonoid(Term* orig, TermEvalResult* evaluatedArgs) const;

  template<class ConstantType, class EvalIneq> 
  LitEvalResult evaluateInequality(Literal* lit, bool strict, EvalIneq evalIneq) const;

  template<class ConstantType, class EvalGround>
  LitEvalResult tryEvalConstant1(Literal* lit, EvalGround fun) const;

  template<class ConstantType, class EvalGround>
  LitEvalResult tryEvalConstant2(Literal* lit, EvalGround fun) const;

  template<class ConstantType, class EvalGround>
  TermEvalResult tryEvalConstant1(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun) const;

  template<class ConstantType, class EvalGround>
  TermEvalResult tryEvalConstant2(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun) const;
};

}

#endif // __POLYNOMIAL_NORMALIZER_HPP__
