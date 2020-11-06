// #include "Kernel/PolynomialNormalizer.hpp"
//

template<class C> using Poly = Polynom<NumTraits<C>>;
#include "Debug/Tracer.hpp"
#include "Lib/STLAllocator.hpp"
#include "Lib/Optional.hpp"
#include <map>

#define TODO throw "TODO";



using LitSimplResult = Inferences::SimplifyingGeneratingLiteralSimplification::Result;


#define IMPL_EVALUATE_PRED(interpretation, ...)                                                               \
  template<>                                                                                                  \
  struct PredicateEvaluator<interpretation> {                                                                 \
    static Optional<LitSimplResult> evaluate(Literal* orig, PolyNf* evaluatedArgs)                                       \
    {                                                                                                         \
      CALL("PredicateEvaluator<" #interpretation ">::evaluate(Literal*,PolyNf*)");                            \
      __VA_ARGS__                                                                                             \
    }                                                                                                         \
  };


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Helper functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class ConstantType, class EvalGround>
Optional<LitSimplResult> tryEvalConstant2(Literal* orig, PolyNf* evaluatedArgs, EvalGround fun) 
{
  using Number = NumTraits<ConstantType>;
  auto& lhs = *evaluatedArgs[0].downcast<Number>().unwrap();
  auto& rhs = *evaluatedArgs[1].downcast<Number>().unwrap();
  if (lhs.isNumber() && rhs.isNumber()) {
    return Optional<LitSimplResult>(LitSimplResult::constant(fun(lhs.unwrapNumber(), rhs.unwrapNumber())));
  } else {
    return Optional<LitSimplResult>();
  }
}



///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Equality
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Number> inline Optional<LitSimplResult> interpretEquality(bool polarity, Perfect<Polynom<Number>> lhs, Perfect<Polynom<Number>> rhs) {
  
  if (lhs->isNumber() && rhs->isNumber()) {
    return Optional<LitSimplResult>(LitSimplResult::constant(polarity == (lhs->unwrapNumber() == rhs->unwrapNumber())));
  } else if (lhs == rhs) {
    return Optional<LitSimplResult>(LitSimplResult::constant(polarity));
  } else {
    return Optional<LitSimplResult>();
  }
}

using IntPoly = Polynom<NumTraits<IntegerConstantType>>;
using RatPoly = Polynom<NumTraits<RationalConstantType>>;
using RealPoly = Polynom<NumTraits<RealConstantType>>;

IMPL_EVALUATE_PRED(Interpretation::EQUAL,
  auto& lhs = evaluatedArgs[0];
  auto& rhs = evaluatedArgs[1];
  auto polarity = orig->polarity();
  auto sort = SortHelper::getEqualityArgumentSort(orig);

  if (lhs == rhs) {
    return Optional<LitSimplResult>(LitSimplResult::constant(polarity));
  }
  switch (sort) {
  case Sorts::SRT_INTEGER:
    return interpretEquality(polarity, lhs.template wrapPoly<IntTraits >(), rhs.template wrapPoly<IntTraits >());
  case Sorts::SRT_RATIONAL:
    return interpretEquality(polarity, lhs.template wrapPoly<RatTraits >(), rhs.template wrapPoly<RatTraits >());
  case Sorts::SRT_REAL:
    return interpretEquality(polarity, lhs.template wrapPoly<RealTraits>(), rhs.template wrapPoly<RealTraits>());
  default:
    return Optional<LitSimplResult>();
  }
)

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Inequalities
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class ConstantType, class EvalIneq> Optional<LitSimplResult> evaluateInequality(Literal* orig, PolyNf* evaluatedArgs, bool strict, EvalIneq evalIneq) {
  ASS(orig->arity() == 2);


  auto lhs = evaluatedArgs[0].template wrapPoly<NumTraits<ConstantType>>();
  auto rhs = evaluatedArgs[1].template wrapPoly<NumTraits<ConstantType>>();

  auto polarity = orig->polarity();
  if (lhs->isNumber() && rhs->isNumber()) {
    return Optional<LitSimplResult>(LitSimplResult::constant(polarity == evalIneq(lhs->unwrapNumber(), rhs->unwrapNumber())));
  } else if (lhs == rhs) {
    return Optional<LitSimplResult>(LitSimplResult::constant(polarity != strict));
  } else {
    return Optional<LitSimplResult>();
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
      // TODO use fastest reminder operation
      return  r.remainderE(l) == IntegerConstantType(0);
  });
)

// TODO
// - include division (?)
// - include binary minus
// - integrate in rebalancing elimination
//     test this case:
//     - eq(mul(2, a), add(x, x)) =====>  eq(a, x)

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES


