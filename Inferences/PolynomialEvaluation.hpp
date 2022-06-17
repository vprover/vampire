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

template<class C>
struct MaybeOverflow
{
  C value;
  bool overflowOccurred;

  MaybeOverflow(C value, bool overflowOccurred) : value(std::move(value)), overflowOccurred(overflowOccurred) {}
  explicit MaybeOverflow(MaybeOverflow const&) = default;
  MaybeOverflow(MaybeOverflow&&) = default;
  MaybeOverflow& operator=(MaybeOverflow&&) = default;

  template<class F>
  auto map(F f)  -> MaybeOverflow<decltype(f(value))>
  { return MaybeOverflow<decltype(f(value))>(f(std::move(value)), overflowOccurred); }
};

template<class C>
std::ostream& operator<<(std::ostream& out, MaybeOverflow<C> const& self) 
{
  out << self.value;
  if (self.overflowOccurred) {
    out << "(overflowed)";
  }
  return out;
}

template<class C>
static MaybeOverflow<C> maybeOverflow(C simplified, bool overflowOccurred) 
{ return MaybeOverflow<C>(std::move(simplified), overflowOccurred); }

template<class A, class F>
MaybeOverflow<A> catchOverflow(F fun, A alternative)
{
  try {
    return maybeOverflow(fun(), false);
  } catch (Kernel::MachineArithmeticException&) {
    return maybeOverflow(std::move(alternative), true);
  }
}

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

  MaybeOverflow<Option<PolyNf>> evaluate(PolyNf in) const;
  template<class NumTraits>
  MaybeOverflow<Option<Perfect<Polynom<NumTraits>>>> evaluate(Perfect<Polynom<NumTraits>> in) const
  { return evaluate(PolyNf(in))
      .map([](auto overf) 
          { return overf.map([](PolyNf p) 
              { return p.template downcast<NumTraits>().unwrap(); }); });
  }

  template<class NumTraits>
  static MaybeOverflow<Polynom<NumTraits>> simplifySummation(Stack<Monom<NumTraits>>, bool removeZeros);
  TermList evaluateToTerm(Term* in) const;
  TermList evaluateToTerm(TermList in) const { return in.isVar() ? in : evaluateToTerm(in.term()); }
  Option<Result> tryEvalPredicate(Literal* orig, PolyNf* evaluatedArgs) const;
private:

  MaybeOverflow<Option<PolyNf>> evaluate(TermList in, SortId sortNumber) const;
  MaybeOverflow<Option<PolyNf>> evaluate(Term* in) const;
  MaybeOverflow<Option<PolyNf>> evaluate(TypedTermList in) const;


  MaybeOverflow<PolyNf> evaluateStep(Term* orig, PolyNf* evaluatedArgs) const;

  mutable Memo::Hashed<PolyNf, MaybeOverflow<PolyNf>, StlHash> _memo;
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
  // TODO make this one the same as in IRCState
  PolynomialEvaluation _inner;
  const bool _alwaysEvaluate;
};

} // namespace Inferences 

#endif /* __POLYNOMIAL_EVALUATION_H__ */
