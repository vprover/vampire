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

// TODO clean up the  messy work split between PolynomialEvaluation, PolynomialEvaluationRule, PolynomialNormalizer and InequalityNormalizer
class PolynomialEvaluation
{
public:
  using Result = SimplifyingGeneratingLiteralSimplification::Result;
  CLASS_NAME(PolynomialEvaluation);
  USE_ALLOCATOR(PolynomialEvaluation);
  PolynomialEvaluation() = delete;
  explicit PolynomialEvaluation(bool removeZeros) 
    : _removeZeros(removeZeros) 
  {  }

  Option<PolyNf> evaluate(PolyNf in) const;
  template<class NumTraits>
  Option<Polynom<NumTraits>> evaluate(Polynom<NumTraits> in) const
  { return evaluate(PolyNf(in))
      .map([](auto overf) 
          { return overf.map([](PolyNf p) 
              { return p.template downcast<NumTraits>().unwrap(); }); });
  }

  template<class NumTraits>
  static PolyNf simplifySummation(Stack<Monom<NumTraits>>, bool removeZeros);
  TermList evaluateToTerm(Term* in) const;
  TermList evaluateToTerm(TermList in) const { return in.isVar() ? in : evaluateToTerm(in.term()); }
  Option<Result> tryEvalPredicate(Literal* orig, PolyNf* evaluatedArgs) const;
private:

  Option<PolyNf> evaluate(TermList in, SortId sortNumber) const;
  Option<PolyNf> evaluate(Term* in) const;
  Option<PolyNf> evaluate(TypedTermList in) const;


  PolyNf evaluateStep(Term* orig, PolyNf* evaluatedArgs) const;

  mutable Memo::Hashed<PolyNf, PolyNf> _memo;
  bool _removeZeros;
};


class PolynomialEvaluationRule
: public SimplifyingGeneratingLiteralSimplification
{
public:
  CLASS_NAME(PolynomialEvaluationRule);
  USE_ALLOCATOR(PolynomialEvaluationRule);

  PolynomialEvaluationRule(Ordering& ordering);
  virtual ~PolynomialEvaluationRule();

private:
  Result simplifyLiteral(Literal*) override;
  // TODO make this one the same as in LascaState
  PolynomialEvaluation _inner;
  const bool _alwaysEvaluate;
};

} // namespace Inferences 

#endif /* __POLYNOMIAL_EVALUATION_H__ */
