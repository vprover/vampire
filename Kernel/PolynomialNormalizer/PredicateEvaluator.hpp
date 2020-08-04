// #include "Kernel/PolynomialNormalizer.hpp"

template<class C> using Poly = Polynom<NumTraits<C>>;
#include "Debug/Tracer.hpp"
#include "Lib/STLAllocator.hpp"
#include "Lib/Optional.hpp"
#include <map>

#define TODO throw "TODO";


// using namespace Lib;

// namespace Kernel {


#define IMPL_EVALUATE_PRED(interpretation, ...)\
  template<>  \
  struct PredicateEvaluator<interpretation> { \
    template<class Config> \
    static LitEvalResult evaluate(Literal* orig, TermEvalResult* evaluatedArgs) \
    { \
      CALL("PredicateEvaluator<" #interpretation ">::evaluate(Literal*,TermEvalResult*)"); \
      __VA_ARGS__ \
    } \
  };


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Helper functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class NormalizerConfig, class ConstantType, class EvalGround>
LitEvalResult tryEvalConstant2(Literal* orig, TermEvalResult* evaluatedArgs, EvalGround fun) {
  auto& lhs = evaluatedArgs[0].asPoly().as<Poly<ConstantType>>();;
  auto& rhs = evaluatedArgs[1].asPoly().as<Poly<ConstantType>>();;
  if (lhs.isCoeff() && rhs.isCoeff()) {
    return LitEvalResult::constant(fun(lhs.unwrapCoeff(), rhs.unwrapCoeff()));
  } else {
    TermList args[] = {
      lhs.template toTerm<NormalizerConfig>(),
      rhs.template toTerm<NormalizerConfig>()
    };
    return LitEvalResult::literal(Literal::create(orig, args));
  }
}



///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Equality
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Config, class number> inline LitEvalResult interpret_equality(bool polarity, Polynom<number> lhs, Polynom<number> rhs) {
  
  if (lhs.isCoeff() && rhs.isCoeff()) {
    return LitEvalResult::constant(polarity == (lhs.unwrapCoeff() == rhs.unwrapCoeff()));
  } else {
    auto res = Polynom<number>::cancel(lhs, rhs);

    auto lTerm = std::get<0>(res).template toTerm<Config>();
    auto rTerm = std::get<1>(res).template toTerm<Config>();

    if (lTerm == rTerm) {
      return LitEvalResult::constant(polarity);
    } else {
      return LitEvalResult::literal(Literal::createEquality(polarity, lTerm, rTerm, number::sort));
    }
  }
}

// using IntTraits = NumTraits<IntegerConstantType>;
// using RatTraits = NumTraits<RationalConstantType>;
// using RealTraits = NumTraits<RealConstantType>;

using IntPoly = Polynom<NumTraits<IntegerConstantType>>;
using RatPoly = Polynom<NumTraits<RationalConstantType>>;
using RealPoly = Polynom<NumTraits<RealConstantType>>;

template<class PolyType> PolyType cvtPoly(TermEvalResult& t) {
  return t.match<PolyType>(
      [](TermList& t) { return PolyType(t); },
      [](AnyPoly&  p) { return PolyType(p.as<PolyType>()); }
      );
}

IMPL_EVALUATE_PRED(Interpretation::EQUAL,
  auto& lhs = evaluatedArgs[0];
  auto& rhs = evaluatedArgs[1];
  auto polarity = orig->polarity();
  auto sort = SortHelper::getEqualityArgumentSort(orig);

  auto shallCancel  = lhs.isPoly() || rhs.isPoly();

  if (shallCancel) {
    switch (sort) {
    case Sorts::SRT_INTEGER:
      return interpret_equality<Config>(polarity, cvtPoly<IntPoly>(lhs), cvtPoly<IntPoly>(rhs));
    case Sorts::SRT_RATIONAL:
      return interpret_equality<Config>(polarity, cvtPoly<RatPoly>(lhs), cvtPoly<RatPoly>(rhs));
    case Sorts::SRT_REAL:
      return interpret_equality<Config>(polarity, cvtPoly<RealPoly>(lhs), cvtPoly<RealPoly>(rhs));
      default:
      // polynomials can only be of number sorts
        ASSERTION_VIOLATION
    }
  } else {
    auto l = lhs.as<TermList>();
    auto r = rhs.as<TermList>();
    if (l == r) {
      return LitEvalResult::constant(polarity);
    } else {
      return LitEvalResult::literal(Literal::createEquality(polarity, l, r, sort));
    }
  }
  //                            //TODO lift to term algebras
)

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Inequalities
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class NormalizerConfig, class ConstantType, class EvalIneq> LitEvalResult evaluateInequality(Literal* orig, TermEvalResult* evaluatedArgs, bool strict, EvalIneq evalIneq) {
  ASS(orig->arity() == 2);


  auto lhs_ = cvtPoly<Poly<ConstantType>>(evaluatedArgs[0]);
  auto rhs_ = cvtPoly<Poly<ConstantType>>(evaluatedArgs[1]);

  // auto shallCancel = lhs.isPoly() || rhs.isPoly();
  auto res = Poly<ConstantType>::cancel(lhs_, rhs_);
  auto lhs = get<0>(res);
  auto rhs = get<1>(res);

  auto polarity = orig->polarity();
  // TODO handle case a <= a + 3 ===> true
  if (lhs.isCoeff() && rhs.isCoeff()) {
    return LitEvalResult::constant(polarity == evalIneq(lhs.unwrapCoeff(), rhs.unwrapCoeff()));
  } else {
    TermList lTerm = lhs.template toTerm<NormalizerConfig>();
    TermList rTerm = rhs.template toTerm<NormalizerConfig>();;
    if (lTerm == rTerm) return LitEvalResult::constant(polarity != strict);

    TermList args[] = {
      lTerm,
      rTerm,
    };
    return LitEvalResult::literal(Literal::create(orig, args));
  }
}

#define __IMPL_INEQ(Const, name, STRICT, op) \
  IMPL_EVALUATE_PRED(NumTraits<Const>::name ## I,  \
       return evaluateInequality<Config, Const>(orig, evaluatedArgs, STRICT, [](Const l, Const r) {return l op r;});  \
  ) \

#define IMPL_INEQUALTIES(Const) \
   /*                inequality| is strict? | operator */ \
  __IMPL_INEQ(Const, less      ,   true     ,  <        ) \
  __IMPL_INEQ(Const, leq       ,   false    ,  <=       ) \
  __IMPL_INEQ(Const, greater   ,   true     ,  >        ) \
  __IMPL_INEQ(Const, geq       ,   false    ,  >=       ) \


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

// void Lib::integrity<Kernel::TermEvalResult>::check(const Kernel::TermEvalResult& self, const char* file, int line) {
//   integrity<Lib::Coproduct<Kernel::TermList, Kernel::AnyPoly>>::check(self, file, line);
// }


