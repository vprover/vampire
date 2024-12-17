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
  auto out = rhs == some(Numeral(0))  ?  none<PolyNf>()
           : rhs.isSome() && rhs.unwrap() == Numeral(1) ? 
                   some<PolyNf>(evalArgs[0])
           : lhs.isSome() && rhs.isSome()  ? 
                   some<PolyNf>(PolyNf(AnyPoly(perfect(Polynom<Number>(f(lhs.unwrap(), rhs.unwrap())))))) 
           : none<PolyNf>();
  return out;
}

template<class Number, class NumEval>
Option<PolyNf> trySimplifyRemainder(PolyNf* evalArgs, NumEval f) 
{
  using Numeral = typename Number::ConstantType;
  auto lhs = evalArgs[0].template tryNumeral<Number>();
  auto rhs = evalArgs[1].template tryNumeral<Number>();
  if (rhs == some(Numeral(0))) {
    return none<PolyNf>();

  } if (rhs.isSome() && rhs.unwrap() == Numeral(1)) {
    return some<PolyNf>(PolyNf(AnyPoly(perfect(Polynom<Number>(Numeral(0))))));
  } else if (lhs.isSome() && rhs.isSome()) {
    return some(PolyNf(AnyPoly(perfect(Polynom<Number>(f(lhs.unwrap(), rhs.unwrap()))))));
  } else {
    return none<PolyNf>();
  }
}

#define IMPL_QUOTIENT_REMAINDER(X)                                                        \
  template<>                                                                              \
  struct FunctionEvaluator<Interpretation::INT_QUOTIENT_ ## X>                            \
  {                                                                                       \
    static Option<PolyNf> simplify(PolyNf* evalArgs)                                      \
    { return trySimplifyQuotient<IntTraits>(evalArgs,                                     \
        [](IntegerConstantType lhs, IntegerConstantType rhs)                              \
        { return lhs.quotient ## X(rhs); });                                              \
    }                                                                                     \
  };                                                                                      \
                                                                                          \
  template<>                                                                              \
  struct FunctionEvaluator<Interpretation::INT_REMAINDER_ ## X>                           \
  {                                                                                       \
    static Option<PolyNf> simplify(PolyNf* evalArgs)                                      \
    { return trySimplifyRemainder<IntTraits>(evalArgs,                                    \
        [](IntegerConstantType lhs, IntegerConstantType rhs)                              \
        { return lhs.remainder ## X(rhs); });                                             \
    }                                                                                     \
  };                                                                                      \

IMPL_QUOTIENT_REMAINDER(T)
IMPL_QUOTIENT_REMAINDER(F)
IMPL_QUOTIENT_REMAINDER(E)

#undef IMPL_QUOTIENT_REMAINDER


#define IMPL_DIVISION(NumTraits)                                                          \
  template<>                                                                              \
  struct FunctionEvaluator<NumTraits::divI>                                               \
  {                                                                                       \
    static Option<PolyNf> simplify(PolyNf* evalArgs)                                      \
    {                                                                                     \
      using Numeral = typename NumTraits::ConstantType;                                   \
      auto lhs = evalArgs[0].tryNumeral<NumTraits>();                                     \
      auto rhs = evalArgs[1].tryNumeral<NumTraits>();                                     \
      if (rhs == some(Numeral(1))) {                                                      \
        return some(evalArgs[0]);                                                         \
      } else if (lhs.isSome() && rhs.isSome() && rhs.unwrap() != Numeral(0)) {            \
        return some(PolyNf(AnyPoly(perfect(Polynom<NumTraits>(lhs.unwrap() / rhs.unwrap()))))); \
      } else {                                                                            \
        return none<PolyNf>();                                                            \
      }                                                                                   \
    }                                                                                     \
  };                                                                                      \

IMPL_DIVISION(RatTraits)
IMPL_DIVISION(RealTraits)

template<class NumTraits>
bool isInteger(MonomFactors<NumTraits> const& m);

template<class NumTraits>
bool isInteger(Polynom<NumTraits> const& m) {
  return m.iterSummands()
    .all([](auto const& monom) 
        { return monom.numeral.isInt() && isInteger(*monom.factors); });
}

template<class NumTraits>
bool isInteger(FuncTerm const& term, NumTraits) 
{ return NumTraits::isFloor(term.function().id()); }

bool isInteger(FuncTerm const& term, IntTraits) 
{ return true; }

template<class NumTraits>
bool isInteger(PolyNf const& term) {
  if (auto num = term.template tryNumeral<NumTraits>()) {
    return num->isInt();

  } else if (auto ft = term.tryFuncTerm()) {
    return isInteger(**ft, NumTraits{});

  } else if (auto var = term.tryVar()) {
    return std::is_same_v<IntTraits, NumTraits>;

  } else {
      return term.downcast<NumTraits>()
        .map([](auto poly){ return isInteger(*poly); })
        .unwrap();
  }
}

template<class NumTraits>
bool isInteger(MonomFactors<NumTraits> const& m) {
  return m.iter()
    .all([](auto const& factor) { 
        return factor.power == 0 || 
          (factor.power > 0 && isInteger<NumTraits>(factor.term));
    });
};


template<class NumTraits>
inline Option<PolyNf> simplFloor(PolyNf* evalArgs)
{
  using Numeral = typename NumTraits::ConstantType;
  auto inner = evalArgs[0].tryNumeral<NumTraits>();
  if (inner) {
    return some(PolyNf::fromNumeral(Numeral(inner->floor())));
  }  else {
    auto poly = evalArgs[0].wrapPoly<NumTraits>();
    // floor(s1 + ... + sn + t1 + ... + tm) ===> s1 + ... + sn + floor(t1 + ... + tn)
    //                              pulledOut <--^^^^^^^^^^^^^         ^^^^^^^^^^^^^--> keptIn
    Recycled<Stack<Monom<NumTraits>>> pulledOut;
    Recycled<Stack<Monom<NumTraits>>> keptIn;
    for (auto monom : poly->iterSummands()) {
      auto k = monom.numeral;
      auto t = monom.factors;
      if (isInteger(*t)) {
        // floor(t + k t) ==> floor(t + (k - i) t) + i t
        //   where t is an integer and
        //         i = floor(k)
        auto i = Numeral(k.floor());
        if (i       != 0) { pulledOut->push(Monom(i   , t)); }
        if ((k - i) != 0) { keptIn->   push(Monom(k -i, t)); }
      } else {
        keptIn->push(monom);
      }
    }

    if (pulledOut->size() == 0) {
      return {};

    } else {


      if (keptIn->size() == 0) {

      } else if (keptIn->size() == 1 && (*keptIn)[0].isNumeral()) { 
        auto numFloor = Numeral((*keptIn)[0].tryNumeral()->floor());
        if (numFloor != 0)
          pulledOut->push(Monom<NumTraits>(numFloor));
      } else {
        auto innerSum = PolyNf(AnyPoly(perfect(Polynom<NumTraits>(std::move(*keptIn)))));
        auto floorTerm = PolyNf(perfect(FuncTerm(FuncId::fromInterpretation(NumTraits::floorI), &innerSum)));
        pulledOut->push(Monom<NumTraits>(Numeral(1), perfect(MonomFactors<NumTraits>(floorTerm))));
      }


      std::sort(pulledOut->begin(), pulledOut->end());

      auto out = PolyNf(AnyPoly(perfect(Polynom<NumTraits>(std::move(*pulledOut)))));
      return some(out);
    }
  }
}

#define IMPL_FLOOR(NumTraits)                                                             \
  template<>                                                                              \
  struct FunctionEvaluator<NumTraits::floorI>                                             \
  {                                                                                       \
    static Option<PolyNf> simplify(PolyNf* evalArgs)                                      \
    { return simplFloor<NumTraits>(evalArgs); }                                           \
  };                                                                                      \

IMPL_FLOOR(RatTraits)
IMPL_FLOOR(RealTraits)

#undef IMPL_DIVISION
