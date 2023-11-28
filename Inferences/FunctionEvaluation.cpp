/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Inferences/PolynomialEvaluation.hpp"
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

template<class NumTraits>
MaybeOverflow<Option<PolyNf>> simplifyFloor(MaybeOverflow<PolyNf>* evalArgs)
{
  using Numeral = typename NumTraits::ConstantType;

  Perfect<Polynom<NumTraits>> inner = evalArgs[0].value.template wrapPoly<NumTraits>();

  auto overflowOccurred = evalArgs[0].overflowOccurred;
  if (inner->isNumber()) {
    return maybeOverflow(some(PolyNf(AnyPoly(perfect(Polynom<NumTraits>(inner->unwrapNumber().floor()))))), overflowOccurred);
  } else {
    Stack<Monom<NumTraits>> inside;
    Stack<Monom<NumTraits>> outside;
    for (auto m : inner->iterSummands()) {
      if (m.factors->isOne() || m.factors->isFloor()) {
        auto c = m.numeral;
        if (Numeral(0) != c.floor()) {
          outside.push(Monom<NumTraits>(c.floor(), m.factors));
        }
        if (c != c.floor()) {
          inside.push(Monom<NumTraits>(c - c.floor(), m.factors));
        }
      } else {
        inside.push(m);
      }
    }
    auto toPoly = [](auto inside) { return PolyNf(AnyPoly(perfect(Polynom<NumTraits>(std::move(inside))))); };
    if (inside.size() != 0) {
      auto fInside = Monom<NumTraits>(MonomFactors<NumTraits>(PolyNf(perfect(FuncTerm(FuncId::fromFunctor(NumTraits::floorF(), Stack<TermList>{}), { toPoly(std::move(inside)) })))));
      outside.push(fInside);
      outside.sort();
    }
    return maybeOverflow(some(toPoly(std::move(outside))), overflowOccurred);
  // } else {
  //   return maybeOverflow(none<PolyNf>(), false);
  }
  // auto lhs = evalArgs[0].value.tryNumeral<NumTraits>();
  // auto rhs = evalArgs[1].value.tryNumeral<NumTraits>();
  // if (rhs == some(Numeral(1))) {
  //   return maybeOverflow(some(evalArgs[0].value), evalArgs[0].overflowOccurred);
  // } else if (lhs.isSome() && rhs.isSome() && rhs.unwrap() != Numeral(0)) {
  //   return catchOverflow(
  //       [&](){ return some(PolyNf(AnyPoly(perfect(Polynom<NumTraits>(lhs.unwrap() / rhs.unwrap()))))); },
  //       none<PolyNf>());
  // } else {
  //   return maybeOverflow(none<PolyNf>(), evalArgs[0].overflowOccurred || evalArgs[1].overflowOccurred);
  // }
};

template<>
struct FunctionEvaluator<RatTraits::floorI>
{
  static MaybeOverflow<Option<PolyNf>> simplify(MaybeOverflow<PolyNf>* evalArgs)
  { return simplifyFloor<RatTraits>(evalArgs); }
};

template<>
struct FunctionEvaluator<RealTraits::floorI>
{
  static MaybeOverflow<Option<PolyNf>> simplify(MaybeOverflow<PolyNf>* evalArgs)
  { return simplifyFloor<RealTraits>(evalArgs); }
};

