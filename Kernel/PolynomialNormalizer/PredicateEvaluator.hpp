// #include "Kernel/PolynomialNormalizer.hpp"

template<class C> using Poly = Polynom<NumTraits<C>>;
#include "Debug/Tracer.hpp"
#include "Lib/STLAllocator.hpp"
#include "Lib/Optional.hpp"
#include <map>

#define TODO throw "TODO";


// using namespace Lib;

// namespace Kernel {


#define IMPL_EVALUATE_PRED(interpretation, ...)                                                               \
  template<>                                                                                                  \
  struct PredicateEvaluator<interpretation> {                                                                 \
    template<class Config>                                                                                    \
    static Optional<LitEvalResult> evaluate(Literal* orig, PolyNf* evaluatedArgs)                                       \
    {                                                                                                         \
      CALL("PredicateEvaluator<" #interpretation ">::evaluate(Literal*,PolyNf*)");                            \
      __VA_ARGS__                                                                                             \
    }                                                                                                         \
  };


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Helper functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class NormalizerConfig, class ConstantType, class EvalGround>
Optional<LitEvalResult> tryEvalConstant2(Literal* orig, PolyNf* evaluatedArgs, EvalGround fun) 
{
  using Number = NumTraits<ConstantType>;
  auto& lhs = evaluatedArgs[0].asPoly().downcast<Number>();
  auto& rhs = evaluatedArgs[1].asPoly().downcast<Number>();
  if (lhs.isNumber() && rhs.isNumber()) {
    return Optional<LitEvalResult>(LitEvalResult::constant(fun(lhs.unwrapNumber(), rhs.unwrapNumber())));
  } else {
    return Optional<LitEvalResult>();
  }
}



///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Equality
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Config, class number> inline Optional<LitEvalResult> interpretEquality(bool polarity, Polynom<number> lhs, Polynom<number> rhs) {
  
  if (lhs.isNumber() && rhs.isNumber()) {
    return Optional<LitEvalResult>(LitEvalResult::constant(polarity == (lhs.unwrapNumber() == rhs.unwrapNumber())));
  } else {
    auto res = Polynom<number>::cancelAdd(lhs, rhs);
    // auto res = Polynom<number>::cancelMul(move(res_.lhs), move(res_.rhs));
    // TODO cancel mul as well

    auto lTerm = res.lhs.toTerm();
    auto rTerm = res.rhs.toTerm();

    if (lTerm == rTerm) {
      return Optional<LitEvalResult>(LitEvalResult::constant(polarity));
    } else if (res.lhs == lhs && res.rhs == rhs) {
      return Optional<LitEvalResult>();
    } else {
      return Optional<LitEvalResult>(LitEvalResult::literal(Literal::createEquality(polarity, lTerm, rTerm, number::sort)));
    }
  }
}

// using IntTraits = NumTraits<IntegerConstantType>;
// using RatTraits = NumTraits<RationalConstantType>;
// using RealTraits = NumTraits<RealConstantType>;

using IntPoly = Polynom<NumTraits<IntegerConstantType>>;
using RatPoly = Polynom<NumTraits<RationalConstantType>>;
using RealPoly = Polynom<NumTraits<RealConstantType>>;

// template<class PolyType> PolyType cvtPoly(PolyNf& t) {
//   return t.match<PolyType>(
//       [](TermList& t) { return PolyType(t); },
//       [](AnyPoly&  p) { return PolyType(p.as<PolyType>()); }
//       );
// }

IMPL_EVALUATE_PRED(Interpretation::EQUAL,
  auto& lhs = evaluatedArgs[0];
  auto& rhs = evaluatedArgs[1];
  auto polarity = orig->polarity();
  auto sort = SortHelper::getEqualityArgumentSort(orig);

  auto shallCancel  = lhs.isPoly() || rhs.isPoly();

  if (shallCancel) {
    switch (sort) {
    case Sorts::SRT_INTEGER:
      return interpretEquality<Config>(polarity, *intoPoly<IntTraits>(lhs), *intoPoly<IntTraits>(rhs));
    case Sorts::SRT_RATIONAL:
      return interpretEquality<Config>(polarity, *intoPoly<RatTraits>(lhs), *intoPoly<RatTraits>(rhs));
    case Sorts::SRT_REAL:
      return interpretEquality<Config>(polarity, *intoPoly<RealTraits>(lhs), *intoPoly<RealTraits>(rhs));
      default:
      // polynomials can only be of number sorts
        ASSERTION_VIOLATION
    }
  } else {
    if (lhs == rhs) {
      return Optional<LitEvalResult>(LitEvalResult::constant(polarity));
    } else {
      return Optional<LitEvalResult>();
    }
  }
  //                            //TODO lift to term algebras
)

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Inequalities
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class NormalizerConfig, class ConstantType, class EvalIneq> Optional<LitEvalResult> evaluateInequality(Literal* orig, PolyNf* evaluatedArgs, bool strict, EvalIneq evalIneq) {
  ASS(orig->arity() == 2);


  auto lhsOrig = *intoPoly<NumTraits<ConstantType>>(evaluatedArgs[0]);
  auto rhsOrig = *intoPoly<NumTraits<ConstantType>>(evaluatedArgs[1]);

  // auto shallCancel = lhs.isPoly() || rhs.isPoly();
  auto res = Poly<ConstantType>::cancelAdd(lhsOrig, rhsOrig);
  auto lhs = res.lhs;
  auto rhs = res.rhs;

  auto polarity = orig->polarity();
  if (lhs.isNumber() && rhs.isNumber()) {
    return Optional<LitEvalResult>(LitEvalResult::constant(polarity == evalIneq(lhs.unwrapNumber(), rhs.unwrapNumber())));
  } else {

    TermList lTerm = lhs.toTerm();
    TermList rTerm = rhs.toTerm();;
    if (lTerm == rTerm) {
      return Optional<LitEvalResult>(LitEvalResult::constant(polarity != strict));
    } else if (lhsOrig == lhs && rhsOrig == rhs) {
      return Optional<LitEvalResult>();
    } else {
      TermList args[] = {
        lTerm,
        rTerm,
      };
      return Optional<LitEvalResult>(LitEvalResult::literal(Literal::create(orig, args)));
    }
  }
}

#define __IMPL_INEQ(Const, name, STRICT, op)                                                                  \
  IMPL_EVALUATE_PRED(NumTraits<Const>::name ## I,                                                             \
       return evaluateInequality<Config, Const>(orig, evaluatedArgs, STRICT, [](Const l, Const r) {return l op r;});  \
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
  return tryEvalConstant2<Config, IntegerConstantType>(orig, evaluatedArgs, 
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
// }

// void Lib::integrity<Kernel::PolyNf>::check(const Kernel::PolyNf& self, const char* file, int line) {
//   integrity<Lib::Coproduct<Kernel::TermList, Kernel::AnyPoly>>::check(self, file, line);
// }


