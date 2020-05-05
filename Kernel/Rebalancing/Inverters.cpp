#include "Inverters.hpp"
#include "Debug/Tracer.hpp"

namespace Kernel {
namespace Rebalancing {
namespace Inverters {
#define DEBUG(...) //DBG(__VA_ARGS__)

#define CASE_INVERT(sort, fun, expr)                                           \
  case num_traits<sort>::fun##I: {                                             \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-local-typedef\"") \
    using number = num_traits<sort>;                                           \
    _Pragma("GCC diagnostic pop") \
    return expr;                                                               \
  }

#define CASE_INVERT_INT(fun, expr) CASE_INVERT(IntegerConstantType, fun, expr)

#define CASE_INVERT_FRAC(fun, expr)                                            \
  CASE_INVERT(RealConstantType, fun, expr) \
  CASE_INVERT(RationalConstantType, fun, expr)

bool canInvertMulInt(const InversionContext &ctxt);
TermList doInvertMulInt(const InversionContext &ctxt);
template <class number> bool nonZero(const TermList &t);

bool NumberTheoryInverter::canInvertTop(const InversionContext &ctxt) {
  CALL("NumberTheoryInverter::canInvertTop")
  auto &t = ctxt.topTerm();
  auto fun = t.functor();

  DEBUG("canInvert ", ctxt.topTerm().toString(), "@", ctxt.topIdx())
  if (theory->isInterpretedFunction(fun)) {
    auto inter = theory->interpretFunction(fun);
    switch (inter) {
      CASE_INVERT_FRAC(add, true)
      CASE_INVERT_FRAC(minus, true)
      CASE_INVERT_FRAC(mul, nonZero<number>(t[1 - ctxt.topIdx()]))
      CASE_INVERT_INT(mul, canInvertMulInt(ctxt))
      CASE_INVERT_INT(add, true)
      CASE_INVERT_INT(minus, true)
    }
    DBG("WARNING: unknown interpreted function: ", t.toString())
    return false;
  } else { /* cannot invert uninterpreted functions */
    DEBUG("no")
    return false;
  }
}



#define CASE_DO_INVERT(sort, fun, expr)                                        \
  case num_traits<sort>::fun##I: {                                             \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-local-typedef\"") \
    using number = num_traits<sort>;                                           \
    return expr;                                                               \
    _Pragma("GCC diagnostic pop") \
  }

#define CASE_DO_INVERT_FRAC(fun, expr)                                         \
  CASE_DO_INVERT(RealConstantType, fun, expr)                                  \
  CASE_DO_INVERT(RationalConstantType, fun, expr)

#define CASE_DO_INVERT_ALL(fun, expr)                                          \
  CASE_DO_INVERT_INT(fun, expr)                                                \
  CASE_DO_INVERT_FRAC(fun, expr)

#define CASE_DO_INVERT_INT(fun, expr)                                          \
  CASE_DO_INVERT(IntegerConstantType, fun, expr)

TermList NumberTheoryInverter::invertTop(const InversionContext &ctxt) {
  auto &t = ctxt.topTerm();
  auto index = ctxt.topIdx();
  auto toWrap = ctxt.toWrap();
  auto fun = t.functor();
  DEBUG("inverting ", ctxt.topTerm().toString())
  ASS(theory->isInterpretedFunction(fun))
  switch (theory->interpretFunction(fun)) {
    CASE_DO_INVERT_ALL(add, number::add(toWrap, number::minus(t[1 - index])))
    CASE_DO_INVERT_ALL(minus, number::minus(toWrap))
    CASE_DO_INVERT_FRAC(
        mul, number::mul(toWrap, number::div(number::one(), t[1 - index])))
    CASE_DO_INVERT_INT(mul, doInvertMulInt(ctxt))
  default:
    ASSERTION_VIOLATION;
  }
};

/** (a * t1) = (t2 * b)
 *  ^^^^^^^^ ctxt.topTerm()
 *       ^^  ctxt.toUnwrap()
 */
struct IntMulInversion {
  TermList t1;
  TermList t2;
  IntegerConstantType a;
  IntegerConstantType b;
};

bool tryInvertMulInt(const InversionContext &ctxt, IntMulInversion &inv) {

  using number = num_traits<IntegerConstantType>;

  auto a_ = ctxt.topTerm()[1 - ctxt.topIdx()];
  IntegerConstantType a;
  if (ctxt.toWrap().isTerm() && theory->tryInterpretConstant(a_, a)) {

    auto &wrap = *ctxt.toWrap().term();
    ASS(ctxt.topTerm().arity() == 2)
    /* (a * t1) = f(...)
     *             ^^^^^^ wrap
     */

    IntegerConstantType b;

    if (wrap.functor() == ctxt.topTerm().functor()) {
      /* (a * t1) = (_ * _)
       *            ^^^^^^^ wrap
       */
      for (int i = 0; i < 2; i++) {
        if (theory->tryInterpretConstant(wrap[i], b) && a.divides(b)) {
          inv = IntMulInversion{
              .t1 = ctxt.toUnwrap(),
              .t2 = wrap[1 - i],
              .a = a,
              .b = b,
          };
          return true;
        }
      }
    } else if (theory->tryInterpretConstant(&wrap, b)) {

      /* (a * t1) = b * 1
       *            ^ wrap
       */
      if (a.divides(b)) {
        inv = IntMulInversion{
            .t1 = ctxt.toUnwrap(),
            .t2 = number::one(),
            .a = a,
            .b = b,
        };
        return true;
      } else if (b == number::zeroC && a != number::zeroC) {
        inv = IntMulInversion{
            .t1 = ctxt.toUnwrap(),
            .t2 = number::zero(),
            .a = a,
            .b = b,
        };
        return true;
      } else {
        return false;
      }
    }
  }
  return false;
}

TermList doInvertMulInt(const InversionContext &ctxt) {
  using number = num_traits<IntegerConstantType>;
  IntMulInversion inv;
  ALWAYS(tryInvertMulInt(ctxt, inv));
  /** (a * t1) = (t2 * b)
   * ===================== where a * c = b
   *  t1 = (t2 * c)
   */
  ASS(inv.a.divides(inv.b) || inv.b == number::zeroC);
  auto c = theory->representConstant(inv.b / inv.a);
  return number::mul(inv.t2, TermList(c));
}

bool canInvertMulInt(const InversionContext &ctxt) {
  IntMulInversion _inv;
  return tryInvertMulInt(ctxt, _inv);
}

template <class number> bool nonZero(const TermList &t) {
  typename number::ConstantType c;
  return theory->tryInterpretConstant(t, c) && number::zeroC != c;
}


} // namespace Inverters
} // namespace Rebalancing
} // namespace Kernel
