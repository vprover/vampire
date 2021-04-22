/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

template<Interpretation i>
struct FunctionEvaluator; 

template<class Number>
MaybeOverflow<Option<PolyNf>> trySimplifyUnaryMinus(MaybeOverflow<PolyNf>* evalArgs)
{
  CALL("trySimplifyUnaryMinus(PolyNf*)")
  using Numeral = typename Number::ConstantType;
  using Polynom = Polynom<Number>;

  auto overflow = evalArgs[0].overflowOccurred;
  auto out = Polynom(*evalArgs[0].value.template wrapPoly<Number>());

  for (unsigned i = 0; i < out.nSummands(); i++) {
     out.summandAt(i).numeral = out.summandAt(i).numeral * Numeral(-1);
  }

  return maybeOverflow(some<PolyNf>(PolyNf(AnyPoly(perfect(std::move(out))))), overflow);
}

template<class Number, class Clsr>
MaybeOverflow<Option<PolyNf>> trySimplifyConst2(MaybeOverflow<PolyNf>* evalArgs, Clsr f) 
{
  auto lhs = evalArgs[0].value.template tryNumeral<Number>();
  auto rhs = evalArgs[1].value.template tryNumeral<Number>();
  auto overflow =  evalArgs[0].overflowOccurred || evalArgs[1].overflowOccurred;
  if (lhs.isSome() && rhs.isSome()) {
    return maybeOverflow(some<PolyNf>(PolyNf(AnyPoly(perfect(Polynom<Number>(f(lhs.unwrap(), rhs.unwrap())))))), overflow);
  } else {
    return maybeOverflow(none<PolyNf>(), overflow);
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// INT_QUOTIENT_X & INT_REMAINDER_X
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


template<class Number, class NumEval>
MaybeOverflow<Option<PolyNf>> trySimplifyQuotient(MaybeOverflow<PolyNf>* evalArgs, NumEval f) 
{
  using Numeral = typename Number::ConstantType;
  auto lhs = evalArgs[0].value.template tryNumeral<Number>();
  auto rhs = evalArgs[1].value.template tryNumeral<Number>();
  auto overflow =  evalArgs[0].overflowOccurred || evalArgs[1].overflowOccurred;
  auto out = rhs == some(Numeral(0))  ?  none<PolyNf>()
           : rhs.isSome() && rhs.unwrap() == Numeral(1) ? 
                   some<PolyNf>(evalArgs[0].value)
           : lhs.isSome() && rhs.isSome()  ? 
                   some<PolyNf>(PolyNf(AnyPoly(perfect(Polynom<Number>(f(lhs.unwrap(), rhs.unwrap())))))) 
           : none<PolyNf>();
  return maybeOverflow(out, overflow);
}

template<class Number, class NumEval>
MaybeOverflow<Option<PolyNf>> trySimplifyRemainder(MaybeOverflow<PolyNf>* evalArgs, NumEval f) 
{
  using Numeral = typename Number::ConstantType;
  auto lhs = evalArgs[0].value.template tryNumeral<Number>();
  auto rhs = evalArgs[1].value.template tryNumeral<Number>();
  if (rhs == some(Numeral(0))) {
    return maybeOverflow(none<PolyNf>(), evalArgs[0].overflowOccurred || evalArgs[1].overflowOccurred);   

  } if (rhs.isSome() && rhs.unwrap() == Numeral(1)) {
    return maybeOverflow(
              some<PolyNf>(PolyNf(AnyPoly(perfect(Polynom<Number>(Numeral(0)))))), 
              /* overflowed termsr not being used. overflow = */ false);
  } else if (lhs.isSome() && rhs.isSome()) {
    return catchOverflow(
              [&]() {return some(PolyNf(AnyPoly(perfect(Polynom<Number>(f(lhs.unwrap(), rhs.unwrap())))))); },
              none<PolyNf>());
  } else {
    return maybeOverflow(none<PolyNf>(), evalArgs[0].overflowOccurred || evalArgs[1].overflowOccurred);   
  }
}

#define IMPL_QUOTIENT_REMAINDER(X)                                                                            \
  template<>                                                                                                  \
  struct FunctionEvaluator<Interpretation::INT_QUOTIENT_ ## X>                                                \
  {                                                                                                           \
    static MaybeOverflow<Option<PolyNf>> simplify(MaybeOverflow<PolyNf>* evalArgs)                            \
    { return trySimplifyQuotient<IntTraits>(evalArgs,                                                         \
        [](IntegerConstantType lhs, IntegerConstantType rhs)                                                  \
        { return lhs.quotient ## X(rhs); });                                                                  \
    }                                                                                                         \
  };                                                                                                          \
                                                                                                              \
  template<>                                                                                                  \
  struct FunctionEvaluator<Interpretation::INT_REMAINDER_ ## X>                                               \
  {                                                                                                           \
    static MaybeOverflow<Option<PolyNf>> simplify(MaybeOverflow<PolyNf>* evalArgs)                            \
    { return trySimplifyRemainder<IntTraits>(evalArgs,                                                        \
        [](IntegerConstantType lhs, IntegerConstantType rhs)                                                  \
        { return lhs.remainder ## X(rhs); });                                                                 \
    }                                                                                                         \
  };                                                                                                          \

IMPL_QUOTIENT_REMAINDER(T)
IMPL_QUOTIENT_REMAINDER(F)
IMPL_QUOTIENT_REMAINDER(E)

#undef IMPL_QUOTIENT_REMAINDER


#define IMPL_DIVISION(NumTraits)                                                                              \
  template<>                                                                                                  \
  struct FunctionEvaluator<NumTraits::divI>                                                                   \
  {                                                                                                           \
    static MaybeOverflow<Option<PolyNf>> simplify(MaybeOverflow<PolyNf>* evalArgs)                            \
    {                                                                                                         \
      using Numeral = typename NumTraits::ConstantType;                                                       \
      auto lhs = evalArgs[0].value.tryNumeral<NumTraits>();                                                   \
      auto rhs = evalArgs[1].value.tryNumeral<NumTraits>();                                                   \
      if (rhs == some(Numeral(1))) {                                                                          \
        return maybeOverflow(some(evalArgs[0].value), evalArgs[0].overflowOccurred);                          \
      } else if (lhs.isSome() && rhs.isSome() && rhs.unwrap() != Numeral(0)) {                                \
        return catchOverflow(                                                                                 \
            [&](){ return some(PolyNf(AnyPoly(perfect(Polynom<NumTraits>(lhs.unwrap() / rhs.unwrap()))))); }, \
            none<PolyNf>());                                                                                  \
      } else {                                                                                                \
        return maybeOverflow(none<PolyNf>(), evalArgs[0].overflowOccurred || evalArgs[1].overflowOccurred);   \
      }                                                                                                       \
    }                                                                                                         \
  };                                                                                                          \

IMPL_DIVISION(RatTraits)
IMPL_DIVISION(RealTraits)

#undef IMPL_DIVISION
