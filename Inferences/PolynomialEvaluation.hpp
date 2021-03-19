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

class PolynomialEvaluation
: public SimplifyingGeneratingLiteralSimplification
{
public:
  CLASS_NAME(PolynomialEvaluation);
  USE_ALLOCATOR(PolynomialEvaluation);

  PolynomialEvaluation(Ordering& ordering);
  virtual ~PolynomialEvaluation();

  MaybeOverflow<Option<PolyNf>> evaluate(PolyNf in) const;
  template<class NumTraits>
  Option<Perfect<Polynom<NumTraits>>> evaluate(Perfect<Polynom<NumTraits>> in) const
  { return evaluate(PolyNf(in)).map([](PolyNf p) { return p.unwrap<Polynom<NumTraits>>(); }); }

  template<class NumTraits>
  static MaybeOverflow<Polynom<NumTraits>> simplifySummation(Stack<Monom<NumTraits>>);
private:

  Result simplifyLiteral(Literal*) override;

  MaybeOverflow<Option<PolyNf>> evaluate(TermList in, SortId sortNumber) const;
  MaybeOverflow<Option<PolyNf>> evaluate(Term* in) const;
  MaybeOverflow<Option<PolyNf>> evaluate(TypedTermList in) const;

  Option<Result> tryEvalPredicate(Literal* orig, PolyNf* evaluatedArgs) const;

  MaybeOverflow<PolyNf> evaluateStep(Term* orig, PolyNf* evaluatedArgs) const;
};


} // namespace Inferences 

#endif /* __POLYNOMIAL_EVALUATION_H__ */
