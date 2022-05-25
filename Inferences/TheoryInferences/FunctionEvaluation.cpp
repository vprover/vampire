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
Option<PolyNf> trySimplifyUnaryMinus(PolyNf* evalArgs)
{
  CALL("trySimplifyUnaryMinus(PolyNf*)")
  using Numeral = typename Number::ConstantType;
  using Polynom = Polynom<Number>;

  auto out = Polynom(*evalArgs[0].template wrapPoly<Number>());

  for (unsigned i = 0; i < out.nSummands(); i++) {
     out.summandAt(i).numeral = out.summandAt(i).numeral * Numeral(-1);
  }
  return some<PolyNf>(PolyNf(AnyPoly(perfect(std::move(out)))));
}

template<class Number, class Clsr>
Option<PolyNf> trySimplifyConst2(PolyNf* evalArgs, Clsr f) 
{
  auto lhs = evalArgs[0].template tryNumeral<Number>();
  auto rhs = evalArgs[1].template tryNumeral<Number>();
  if (lhs.isSome() && rhs.isSome()) {
    return some<PolyNf>(PolyNf(AnyPoly(perfect(Polynom<Number>(f(lhs.unwrap(), rhs.unwrap()))))));
  } else {
    return none<PolyNf>();
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// INT_QUOTIENT_X & INT_REMAINDER_X
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Number, class NumEval>
Option<PolyNf> trySimplifyQuotient(PolyNf* evalArgs, NumEval f) 
{
  using Numeral = typename Number::ConstantType;
  auto lhs = evalArgs[0].template tryNumeral<Number>();
  auto rhs = evalArgs[1].template tryNumeral<Number>();
  if (rhs.isSome() && rhs.unwrap() == Numeral(1)) {
    return some<PolyNf>(evalArgs[0]);
  } else if (lhs.isSome() && rhs.isSome()) {
    return some<PolyNf>(PolyNf(AnyPoly(perfect(Polynom<Number>(f(lhs.unwrap(), rhs.unwrap()))))));
  } else {
    return none<PolyNf>();
  }
}

template<class Number, class NumEval>
Option<PolyNf> trySimplifyRemainder(PolyNf* evalArgs, NumEval f) 
{
  using Numeral = typename Number::ConstantType;
  auto lhs = evalArgs[0].template tryNumeral<Number>();
  auto rhs = evalArgs[1].template tryNumeral<Number>();
  if (rhs.isSome() && rhs.unwrap() == Numeral(1)) {
    return some<PolyNf>(PolyNf(AnyPoly(perfect(Polynom<Number>(Numeral(0))))));
  } else if (lhs.isSome() && rhs.isSome()) {
    return some<PolyNf>(PolyNf(AnyPoly(perfect(Polynom<Number>(f(lhs.unwrap(), rhs.unwrap()))))));
  } else {
    return none<PolyNf>();
  }
}

#define IMPL_QUOTIENT_REMAINDER(X)                                                                            \
  template<>                                                                                                  \
  struct FunctionEvaluator<Interpretation::INT_QUOTIENT_ ## X>                                                \
  {                                                                                                           \
    static Option<PolyNf> simplify(PolyNf* evalArgs)                                                          \
    { return trySimplifyQuotient<IntTraits>(evalArgs,                                                         \
        [](IntegerConstantType lhs, IntegerConstantType rhs)                                                  \
        { return lhs.quotient ## X(rhs); });                                                                  \
    }                                                                                                         \
  };                                                                                                          \
                                                                                                              \
  template<>                                                                                                  \
  struct FunctionEvaluator<Interpretation::INT_REMAINDER_ ## X>                                               \
  {                                                                                                           \
    static Option<PolyNf> simplify(PolyNf* evalArgs)                                                          \
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
    static Option<PolyNf> simplify(PolyNf* evalArgs)                                                          \
    {                                                                                                         \
      using Numeral = typename NumTraits::ConstantType;                                                       \
      auto lhs = evalArgs[0].tryNumeral<NumTraits>();                                                         \
      auto rhs = evalArgs[1].tryNumeral<NumTraits>();                                                         \
      if (lhs.isSome() && rhs.isSome() && rhs.unwrap() != Numeral(0)) {                                       \
        return Option<PolyNf>(PolyNf(AnyPoly(perfect(Polynom<NumTraits>(lhs.unwrap() / rhs.unwrap())))));     \
      } else {                                                                                                \
        return Option<PolyNf>();                                                                              \
      }                                                                                                       \
    }                                                                                                         \
  };                                                                                                          \

IMPL_DIVISION(RatTraits)
IMPL_DIVISION(RealTraits)

#undef IMPL_DIVISION
