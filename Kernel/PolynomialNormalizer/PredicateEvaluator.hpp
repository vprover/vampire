/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

template<Theory::Interpretation inter>
struct PredicateEvaluator;

template<class C> using Poly = Polynom<NumTraits<C>>;
#include "Debug/Tracer.hpp"
#include "Lib/STLAllocator.hpp"
#include "Lib/Option.hpp"

using LitSimplResult = Inferences::SimplifyingGeneratingLiteralSimplification::Result;


#define IMPL_EVALUATE_PRED(interpretation, ...)                                                               \
  template<>                                                                                                  \
  struct PredicateEvaluator<interpretation> {                                                                 \
    static Option<LitSimplResult> evaluate(Literal* orig, PolyNf* evaluatedArgs)                              \
    {                                                                                                         \
      CALL("PredicateEvaluator<" #interpretation ">::evaluate(Literal*,PolyNf*)");                            \
      __VA_ARGS__                                                                                             \
    }                                                                                                         \
  };


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Helper functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class ConstantType, class EvalGround>
Option<LitSimplResult> tryEvalConstant2(Literal* orig, PolyNf* evaluatedArgs, EvalGround fun) 
{
  using Number = NumTraits<ConstantType>;
  auto& lhs = *evaluatedArgs[0].downcast<Number>().unwrap();
  auto& rhs = *evaluatedArgs[1].downcast<Number>().unwrap();
  if (lhs.isNumber() && rhs.isNumber()) {
    return Option<LitSimplResult>(LitSimplResult::constant(fun(lhs.unwrapNumber(), rhs.unwrapNumber())));
  } else {
    return Option<LitSimplResult>();
  }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Equality
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Number> inline Option<LitSimplResult> interpretEquality(bool polarity, Perfect<Polynom<Number>> lhs, Perfect<Polynom<Number>> rhs) {
  if (lhs->isNumber() && rhs->isNumber()) {
    return Option<LitSimplResult>(LitSimplResult::constant(polarity == (lhs->unwrapNumber() == rhs->unwrapNumber())));
  } else if (lhs == rhs) {
    return Option<LitSimplResult>(LitSimplResult::constant(polarity));
  } else {
    return Option<LitSimplResult>();
  }
}

using IntPoly = Polynom<NumTraits<IntegerConstantType>>;
using RatPoly = Polynom<NumTraits<RationalConstantType>>;
using RealPoly = Polynom<NumTraits<RealConstantType>>;

IMPL_EVALUATE_PRED(Interpretation::EQUAL,
  auto& lhs = evaluatedArgs[0];
  auto& rhs = evaluatedArgs[1];
  auto polarity = orig->polarity();
  DEBUG("evaluating ", lhs, polarity ? " = " : " /= ", rhs)
  auto sort = SortHelper::getEqualityArgumentSort(orig);

  if (lhs == rhs) {
    return Option<LitSimplResult>(LitSimplResult::constant(polarity));
  }
  if (sort == IntTraits::sort())
    return interpretEquality(polarity, lhs.template wrapPoly<IntTraits >(), rhs.template wrapPoly<IntTraits >());
  if (sort == RatTraits::sort())
    return interpretEquality(polarity, lhs.template wrapPoly<RatTraits >(), rhs.template wrapPoly<RatTraits >());
  if (sort == RealTraits::sort())
    return interpretEquality(polarity, lhs.template wrapPoly<RealTraits>(), rhs.template wrapPoly<RealTraits>());
  else
    return Option<LitSimplResult>();
)

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Inequalities
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class ConstantType, class EvalIneq> Option<LitSimplResult> evaluateInequality(Literal* orig, PolyNf* evaluatedArgs, bool strict, EvalIneq evalIneq) {
  ASS(orig->arity() == 2);


  auto lhs = evaluatedArgs[0].template wrapPoly<NumTraits<ConstantType>>();
  auto rhs = evaluatedArgs[1].template wrapPoly<NumTraits<ConstantType>>();

  auto polarity = orig->polarity();
  if (lhs->isNumber() && rhs->isNumber()) {
    return Option<LitSimplResult>(LitSimplResult::constant(polarity == evalIneq(lhs->unwrapNumber(), rhs->unwrapNumber())));
  } else if (lhs == rhs) {
    return Option<LitSimplResult>(LitSimplResult::constant(polarity != strict));
  } else {
    return Option<LitSimplResult>();
  }
}

#define __IMPL_INEQ(Const, name, STRICT, op)                                                                  \
  IMPL_EVALUATE_PRED(NumTraits<Const>::name ## I,                                                             \
       return evaluateInequality<Const>(orig, evaluatedArgs, STRICT, [](Const l, Const r) {return l op r;});  \
  )                                                                                                           \
;
#define IMPL_INEQUALTIES(Const)                                                                               \
   /*                inequality| is strict? | operator */                                                     \
  __IMPL_INEQ(Const, less      ,   true     ,  <        )                                                     \
  __IMPL_INEQ(Const, leq       ,   false    ,  <=       )                                                     \
  __IMPL_INEQ(Const, greater   ,   true     ,  >        )                                                     \
  __IMPL_INEQ(Const, geq       ,   false    ,  >=       )                                                     \


IMPL_INEQUALTIES(RationalConstantType)
IMPL_INEQUALTIES(RealConstantType) 
IMPL_INEQUALTIES(IntegerConstantType)

#undef  IMPL_NUM_EVALS
#undef  __IMPL_INEQ

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// INT_DIVIDES
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

IMPL_EVALUATE_PRED(Interpretation::INT_DIVIDES,
  return tryEvalConstant2<IntegerConstantType>(orig, evaluatedArgs, 
    [](IntegerConstantType l, IntegerConstantType r) -> bool { 
      return  r.remainderE(l) == IntegerConstantType(0);
  });
)

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// NUM_IS_NUM_DIVIDES
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#define IMPL_EVALUATE_IS(n1,n2, expr)                                                                         \
  IMPL_EVALUATE_PRED(n1 ## Traits::is ## n2 ## I,                                                             \
      using N1Traits = n1##Traits;                                                                            \
      using Numeral1 = typename N1Traits::ConstantType;                                                       \
      return evaluatedArgs[0].tryNumeral<N1Traits>()                                                          \
        .map([](Numeral1 num) -> bool { return expr; })                                                       \
        .map([&](bool x) -> LitSimplResult { return LitSimplResult::constant(orig->polarity() == x); });      \
        )

IMPL_EVALUATE_IS(Int, Int , true)
IMPL_EVALUATE_IS(Int, Rat , true)
IMPL_EVALUATE_IS(Int, Real, true)

IMPL_EVALUATE_IS(Rat, Int , num.denominator() == 1)
IMPL_EVALUATE_IS(Rat, Rat , true)
IMPL_EVALUATE_IS(Rat, Real, true)

IMPL_EVALUATE_IS(Real, Int , num.representation().denominator() == 1)
IMPL_EVALUATE_IS(Real, Rat , [&](){ RationalConstantType x = num.representation(); (void)x; return true;}())
IMPL_EVALUATE_IS(Real, Real, true)

#undef IMPL_EVALUATE_IS
