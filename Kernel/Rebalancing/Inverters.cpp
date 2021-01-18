/*
 * File Inverters.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/NonZeroness.hpp"
#include "Inverters.hpp"
#include "Debug/Tracer.hpp"
#include "Shell/Statistics.hpp"
#include "Lib/Option.hpp"

namespace Kernel {
namespace Rebalancing {
namespace Inverters {
#define DEBUG(...) //DBG(__VA_ARGS__)

using InvRes = InversionResult;

template<class A> void __ignoreWarnUnusedLocalTypedefHack() {}

#define CASE(sort, funI, ...)                                                                                 \
  case NumTraits<sort>::funI:   {                                                                             \
    using Number = NumTraits<sort>;                                                                           \
    __ignoreWarnUnusedLocalTypedefHack<Number>();                                                             \
    __VA_ARGS__                                                                                               \
  }

#define CASE_FRAC(fun, ...)                                                                                   \
  CASE(RealConstantType, fun ,__VA_ARGS__)                                                                    \
  CASE(RationalConstantType, fun, __VA_ARGS__)

#define CASE_INT(fun, ...)                                                                                    \
  CASE(IntegerConstantType, fun ,__VA_ARGS__)                                                                 \

#define CASE_ANY_NUM(fun, ...)                                                                                \
  CASE_FRAC(fun,__VA_ARGS__)                                                                                  \
  CASE_INT(fun,__VA_ARGS__)

template <class Number> bool nonZero(const TermList &t);

bool dtorIsPredicate(Signature::Symbol const& ctor, unsigned index) 
{ return ctor.fnType()->arg(index) == Sorts::SRT_BOOL; }

bool NumberTheoryInverter::canInvertTop(const InversionContext &ctxt) const 
{
  CALL("NumberTheoryInverter::canInvertTop")
  return tryInvertTop(ctxt, nullptr);
}

InvRes NumberTheoryInverter::invertTop(const InversionContext &ctxt) const 
{
  CALL("NumberTheoryInverter::invertTop")
  InvRes out;
  ALWAYS(tryInvertTop(ctxt, &out));
  return out;
}

template <class Number> bool nonZero(const TermList &t) 
{ 
  typename Number::ConstantType c;
  return theory->tryInterpretConstant(t, c) && Number::zeroC != c;
}


template <class Number> Literal* nonZeroGuard(const TermList &t) 
{ return Literal::createEquality(true, Number::zero(), t, Number::sort); }

bool NumberTheoryInverter::tryInvertTop(const InversionContext &ctxt, InversionResult* out) const 
{

  CALL("NumberTheoryInverter::tryInvertTop")
  auto &t = ctxt.topTerm();
  auto index = ctxt.topIdx();
  // we want to rewrite `lhs != t`
  auto lhs = ctxt.toWrap();
  auto fun = t.functor();

  DEBUG("tryInvert ", ctxt.topTerm().toString(), "@", ctxt.topIdx())
  if (theory->isInterpretedFunction(fun)) {
    auto inter = theory->interpretFunction(fun);
    switch (inter) {

      CASE_ANY_NUM(addI, { /* lhs != s + _ ==> _ !=  lhs - s*/
          auto s = t[1 - index];
          if (out) 
            *out = InversionResult::withoutGuards(Number::add(lhs, Number::minus(s)));
          return true;
      })

      CASE_ANY_NUM(minusI, { /* lhs != - _ ==> _ != -lhs*/
          if (out) 
            *out = InversionResult::withoutGuards(Number::minus(lhs));
          return true;
      })

      CASE_FRAC(mulI, { /* lhs != s * rhs ==> rhs != lhs / s  (if s is non-zero )*/
          auto s = t[1 - ctxt.topIdx()];
          if (nonZero<Number>(s) ) {
            if (out) 
              *out = InversionResult::withoutGuards(Number::div(lhs, s));
            return true;
          } else if (_generateGuards && s != Number::zero()) {
            if (out)
              *out = InversionResult::withGuard(
                  Number::div(lhs, s),
                  nonZeroGuard<Number>(s));
            return true;
          } else {
            return false;
          }
      })

      CASE_FRAC(divI, if (index == 0) {   
          /* lhs  != rhs / s ==> rhs != lhs * s ( if s is non-zero ) */
          auto s = t[1 - index];
          if (nonZero<Number>(s)) {
            if (out)
              *out = InversionResult::withoutGuards(Number::mul(lhs, s));
            return true;
          } else if (_generateGuards) {
            if (out) 
              *out = InversionResult::withGuard(Number::mul(lhs, s),
                  nonZeroGuard<Number>(s));
            return true;
          } else {
            return false;
          }
      } else {
        ASS(index == 1)
        /* lhs != s / rhs ==> rhs * lhs != s (if rhs is non-zero )
         *              ==> rhs != s / lhs (is lhs is non-zero ) */
        auto s = t[1 - index];
        auto rhs   = t[index];
        if (nonZero<Number>(lhs) && nonZero<Number>(rhs)) {
          if (out) *out = InversionResult::withoutGuards(Number::div(s, lhs));
        } else if (_generateGuards) {
          if (out) {
            Stack<Literal*> guards(2 - ((unsigned) nonZero<Number>(lhs) + (unsigned) nonZero<Number>(rhs)));
            if (!nonZero<Number>(lhs)) guards.push(nonZeroGuard<Number>(lhs));
            if (!nonZero<Number>(rhs)) guards.push(nonZeroGuard<Number>(rhs));
            *out = InversionResult(Number::div(s, lhs), std::move(guards));
          }
          return true;
        }
      })

      CASE_INT(mulI, { /* lhs != rhs * s ==> rhs != lhs * s ( if s in {1, -1} ) */
          auto s = t[1 - index];
          if (   Number::tryNumeral(s) == Option<IntegerConstantType>(Number::constant(1)) 
              || Number::tryNumeral(s) == Option<IntegerConstantType>(Number::constant(-1))) {
            if (out) *out = InversionResult::withoutGuards(Number::mul(lhs, s));
            return true;
          } else {
            return false;
          }
      })

    // case Theory::Interpretation::ARRAY_STORE:
    //   /* store(t, i, x) = s ==> x = select(s, i) */
    //   return ctxt.topIdx() == 2;
      default:;
    }
    // DBG("WARNING: unknown interpreted function: ", t.toString())
    return false;
  } else { 
    /* cannot invert uninterpreted functions */
    return false;
  }
}

} // namespace Inverters
} // namespace Rebalancing
} // namespace Kernel
