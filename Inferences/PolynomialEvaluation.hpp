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

#include "Kernel/Polynomial.hpp"

#include "InferenceEngine.hpp"

namespace Inferences 
{

using SortId = TermList;

// TODO clean up the  messy work split between PolynomialEvaluation, PolynomialEvaluationRule, PolynomialNormalizer and InequalityNormalizer
class PolynomialEvaluation
{
public:

  template<class NumTraits>
  static PolyNf simplifySummation(Stack<Monom<NumTraits>>, bool removeZeros);
  TermList evaluateToTerm(Term* in) const;
  TermList evaluateToTerm(TermList in) const { return in.isVar() ? in : evaluateToTerm(in.term()); }
  Option<Inferences::SimplifyingGeneratingLiteralSimplification::Result> tryEvalPredicate(Literal* orig, PolyNf* evaluatedArgs) const;
  Option<PolyNf> evaluate(PolyNf normalized) const;
private:

  Option<PolyNf> evaluate(TermList in, SortId sortNumber) const;
  Option<PolyNf> evaluate(Term* in) const;
  Option<PolyNf> evaluate(TypedTermList in) const;


  PolyNf evaluateStep(Term* orig, PolyNf* evaluatedArgs) const;

  mutable Memo::Hashed<PolyNf, PolyNf, StlHash> _memo;
};


class PolynomialEvaluationRule
: public SimplifyingGeneratingLiteralSimplification
{
public:

  PolynomialEvaluationRule(Ordering& ordering);
  ~PolynomialEvaluationRule() override;

private:
  Result simplifyLiteral(Literal*) override;
  // TODO make this one the same as in AlascaState
  PolynomialEvaluation _inner;
  const bool _alwaysEvaluate;
};

} // namespace Inferences 

#endif /* __POLYNOMIAL_EVALUATION_H__ */
