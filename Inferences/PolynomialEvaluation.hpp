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

  MaybeOverflow(MaybeOverflow&&) = default;
  MaybeOverflow& operator=(MaybeOverflow&&) = default;

  template<class F>
  auto map(F f)  -> MaybeOverflow<decltype(f(value))>
  { return { .value = f(value), .overflowOccurred = overflowOccurred, }; }
};

template<class C>
static MaybeOverflow<C> maybeOverflow(C simplified, bool overflowOccurred) 
{ return { .value = simplified, .overflowOccurred = overflowOccurred, }; }

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
  static Polynom<NumTraits> simplifySummation(Stack<Monom<NumTraits>>, bool& overflow);
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
