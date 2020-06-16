#include "Kernel/PolynomialNormalizer.hpp"

#include "Debug/Tracer.hpp"
#include "Lib/STLAllocator.hpp"
#include "Lib/Optional.hpp"
#include <map>
#include <stack>
#include "Ordering.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

#define TODO throw "TODO";


using namespace Lib;

namespace Kernel {

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Equality
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number> inline LitEvalResult interpret_equality(Literal* lit, bool polarity, TermList lhs, TermList rhs) {
  using Const = typename number::ConstantType;
  Const l;
  Const r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return LitEvalResult::constant(polarity == (l == r));
  } else {
    return LitEvalResult::literal(Literal::createEquality(lit->polarity(), lhs, rhs, number::sort));
  }
}

template<> LitEvalResult evaluateLit<Interpretation::EQUAL>(Literal* lit) {
  auto lhs = *lit->nthArgument(0);
  auto rhs = *lit->nthArgument(1);
  if (lhs == rhs) return LitEvalResult::constant(lit->polarity());
  auto sort =  SortHelper::getEqualityArgumentSort(lit);
  switch (sort) {
    case Sorts::SRT_INTEGER:  return interpret_equality<NumTraits<IntegerConstantType>>(lit, lit->polarity(), lhs, rhs);
    case Sorts::SRT_RATIONAL: return interpret_equality<NumTraits<RationalConstantType>>(lit, lit->polarity(), lhs, rhs);
    case Sorts::SRT_REAL:     return interpret_equality<NumTraits<RealConstantType>>(lit, lit->polarity(), lhs, rhs);
                             //TODO lift to term algebras
    default:
      return LitEvalResult::literal(Literal::createEquality(lit->polarity(), lhs, rhs, sort));
  }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Inequalities
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class ConstantType, class EvalIneq> LitEvalResult evaluateInequality(Literal* lit, bool strict, EvalIneq evalIneq) {
  ASS(lit->arity() == 2);
  auto lhs = *lit->nthArgument(0);
  auto rhs = *lit->nthArgument(1);
  if (lhs == rhs) return LitEvalResult::constant(lit->polarity() != strict);
  ConstantType l;
  ConstantType r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return LitEvalResult::constant(lit->polarity() == evalIneq(l, r));
  } else {
    return LitEvalResult::literal(lit);
  }
}

#define __IMPL_INEQ(Const, name, STRICT, op) \
  template<> LitEvalResult evaluateLit<NumTraits<Const>::name ## I>(Literal* lit) \
  { return evaluateInequality<Const>(lit, STRICT, [](Const l, Const r) {return l op r;}); } \

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

template<> LitEvalResult evaluateLit<Interpretation::INT_DIVIDES>(Literal* lit) {
  return tryEvalConstant2<IntegerConstantType>(lit, [](IntegerConstantType l, IntegerConstantType r) { 
      return  r.remainderE(l) == IntegerConstantType(0);
  });
}

// TODO
// - include division (?)
// - include binary minus
// - integrate in rebalancing elimination
//     test this case:
//     - eq(mul(2, a), add(x, x)) =====>  eq(a, x)

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES
}

// void Lib::integrity<Kernel::TermEvalResult>::check(const Kernel::TermEvalResult& self, const char* file, int line) {
//   integrity<Lib::Coproduct<Kernel::TermList, Kernel::AnyPoly>>::check(self, file, line);
// }


